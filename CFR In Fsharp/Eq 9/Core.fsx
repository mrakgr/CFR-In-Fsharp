open System.Collections.Generic

// Types

type Infoset = int
type Size = int
//type Player = int // Assumes only one player. This is equivalent to having the other players have only one action in every node.

type GameTree = // Does not use chance nodes.
| Terminal of reward : float
| Response of id : Infoset * branches : GameTree []

type PolicyAtNode = float []
type Policy = Map<Infoset, PolicyAtNode>

// Testing

#r @"..\..\packages\FsCheck.3.0.0-alpha4\lib\net452\FsCheck.dll"
open FsCheck

type TreePolicies = {policies : Policy []; tree : GameTree }

let gen_policy_at_node s : Gen<PolicyAtNode> = 
    let total = 100000
    Gen.piles s total
    |> Gen.map (Array.map (fun x -> float x / float total))
let gen_policy infoset_sizes : Gen<Policy> =
    Array.map gen_policy_at_node infoset_sizes
    |> Gen.sequenceToArr
    |> Gen.map (Array.mapi (fun i x -> i,x) >> Map.ofArray)

let gen_reward = Gen.choose (-100,100) |> Gen.map (fun x -> float x / 10.0)
let gen_terminal = gen_reward |> Gen.map Terminal

/// Picks the ith index not in l.
let count_and_pick (l : Set<int>) =
    assert (Set.forall (fun x -> x >= 0) l)
    let inline gap_empty size next i = if i < size then i else size + next (i - size)
    let inline gap_one next i = 1 + next i
    let c, next = Set.foldBack (fun x' (c, next) -> c+1, fun x i -> gap_empty (x' - x - 1) (gap_one (next x')) i) l (0, (fun x' i -> i))
    c, next -1

let gen_tree : Gen<GameTree * Size []> = Gen.sized <| fun s -> gen {
    let infoset_sizes = ResizeArray()
    let rec response infoset_removed s =
        if s > 0 then
            gen {
                let infoset_removed_count, pick_ith = count_and_pick infoset_removed
                let make_new = gen {
                    let id = infoset_sizes.Count
                    let! infoset_size = Gen.choose(2,5)
                    infoset_sizes.Add infoset_size
                    return infoset_size, id
                    }

                let get_existing = gen {
                    let! id = Gen.choose(0, infoset_sizes.Count-infoset_removed_count-1) |> Gen.map pick_ith
                    let infoset_size = infoset_sizes.[id]
                    return infoset_size, id
                    }

                let! infoset_size, id = Gen.frequency [(infoset_sizes.Count-infoset_removed_count, get_existing); (max 1 infoset_removed_count, make_new)] 

                let! branches = loop (Set.add id infoset_removed) (s/infoset_size) |> Gen.arrayOfLength infoset_size 
                return Response(id,branches)
            }
        else gen_terminal
    and loop infoset_removed s = Gen.frequency [(2, response infoset_removed s); (1, gen_terminal)]

    let! tree = response Set.empty s
    return tree, infoset_sizes.ToArray()
    }

let gen_game num_policies : Gen<TreePolicies> = gen {
    let! tree, infoset_sizes = gen_tree
    let! policies = gen_policy infoset_sizes |> Gen.arrayOfLength num_policies
    return {policies=policies; tree=tree}
    }
    
//gen_game 2
//|> Gen.sample 1

type MyGenerators =
    static member Game = Arb.fromGen (gen_game 2)

Arb.register<MyGenerators>()

//Arb.generate<TreePolicies>
//|> Gen.sampleWithSize 6 10

let error_bound_for_floats = 10.0 ** -7.0
let (=?) a b = abs (a - b) <= error_bound_for_floats