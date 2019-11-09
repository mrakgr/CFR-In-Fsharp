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

let pick_one (x : Set<_>) =
    Gen.choose(0,x.Count-1)
    |> Gen.map (fun i -> Set.fold (fun (i', s) x -> if i = i' then i' + 1, Some x else i' + 1, s) (0, None) x)

let gen_tree s : Gen<GameTree * Size []> = gen {
    let infoset_sizes = ResizeArray()
    //let! (infoset_sizes : Size []) = Gen.choose (2,5) |> Gen.arrayOfLength 1000
    let rec loop infoset_available infoset_removed s =
        if s > 0 then
            gen {
                match! pick_one (infoset_available - infoset_removed) with
                | None -> 
                    let! infoset_size = Gen.choose(2,5)
                    let l = infoset_sizes.Count
                    infoset_sizes.Add(c)
                    let! branches = 
                        Array.init infoset_size (fun _ -> loop (Set.add l infoset_available) (Set.add l infoset_removed) (s/infoset_size)) 
                        |> Gen.sequenceToArr
                    return Response(id,branches)


                if sel.Count = 0 then 
                    let! c = Gen.choose (2,5)
                    infoset_sizes.Add(c)
                    avail.Add(c)
                

                let! (id : Infoset) =
                    
                        gen {
                            
                            let l = infoset_sizes.Count
                            infoset_sizes.Add(c)
                            return infoset_available.Add l
                        }
                    else
                        gen {
                            let! c = Gen.choose(0, infoset_available.Count)
                        }

                //let! (id : Infoset) = Gen.choose (0, infoset_sizes.Length-1)
                let infoset_size = infoset_sizes.[id]

            }
        else gen_terminal
    let! tree = loop Map.empty s
    return tree
    }

let gen_game num_policies num_infosets size : Gen<TreePolicies> = gen {
    let! tree, infoset_sizes = gen_tree num_infosets size
    let! policies = gen_policy infoset_sizes |> Gen.arrayOfLength num_policies
    return {policies=policies; tree=tree; infoset_sizes=infoset_sizes}
    }
    
//gen_game 2 5 10
//|> Gen.sample 1

type MyGenerators =
    static member Game = Arb.fromGen (gen_game 2 5 2)

Arb.register<MyGenerators>()

//Arb.from<TreePolicies>.Generator
//|> Gen.sample 1

let error_bound_for_floats = 10.0 ** -7.0
let (=?) a b = abs (a - b) <= error_bound_for_floats