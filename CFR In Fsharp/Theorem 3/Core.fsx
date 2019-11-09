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

type TreePolicies = {policies : Policy []; tree : GameTree; infoset_sizes: Size []}

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

let gen_tree num_infosets s : Gen<GameTree * Size []> = gen {
    let! (infoset_sizes : Size []) = Gen.choose (2,5) |> Gen.arrayOfLength num_infosets
    let rec loop s =
        Gen.oneof [
            gen_terminal
            if s > 0 then
                gen {
                    let! (id : Infoset) = Gen.choose (0, infoset_sizes.Length-1)
                    let infoset_size = infoset_sizes.[id]
                    let! branches = Array.init infoset_size (fun _ -> loop (s/infoset_size)) |> Gen.sequenceToArr
                    return Response(id,branches)
                }
            else gen_terminal
            ]

    let! tree = loop s
    return tree, infoset_sizes
    }

let gen_game num_policies num_infosets size : Gen<TreePolicies> = gen {
    let! tree, infoset_sizes = gen_tree num_infosets size
    let! policies = gen_policy infoset_sizes |> Gen.arrayOfLength num_policies
    return {policies=policies; tree=tree; infoset_sizes=infoset_sizes}
    }

//gen_game 2 5 10
//|> Gen.sample 1

type MyGenerators =
    static member Game = Arb.fromGen (gen_game 2 5 5)

Arb.register<MyGenerators>()

let error_bound_for_floats = 10.0 ** -7.0
let (=?) a b = abs (a - b) <= error_bound_for_floats