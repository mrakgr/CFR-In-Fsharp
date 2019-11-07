type Infoset = int
type Size = int
type Player = int

type GameTree =
| Terminal of reward : float
| Response of id : Infoset * branches : GameTree []

type PolicyAtNode = float []
type Policy = Map<Infoset, PolicyAtNode>

let sum_succ (id : Infoset) (branches : GameTree []) (o : Policy) f = Array.fold2 (fun s policy branch -> s + policy * f branch) 0.0 o.[id] branches

let u' o f = function
    | Terminal reward -> reward
    | Response (id, branches) -> sum_succ id branches o f

let rec u (o : Policy) tree = u' o (u o) tree

let rec infosets_at_branch = function
    | Terminal _ -> Set.empty
    | Response (id, branches) -> Set.add id (Array.fold (fun s branch -> Set.union s (infosets_at_branch branch)) Set.empty branches)

let update_at_branch_current cur next = function
    | Terminal _ -> cur
    | Response (id, _) -> Map.add id (Map.find id next) cur
let update_at_branch_descent cur next branch = Set.fold (fun s id -> Map.add id (Map.find id next) s) cur (infosets_at_branch branch)

let R (o' : Policy) (o : Policy) (tree : GameTree) = u o' tree - u o tree
let R' (o' : Policy) (o : Policy) (tree : GameTree) =
    u (update_at_branch_current o o' tree) tree - u o tree + 
    // The reason why I am using u' rather than sum_succ is because I need to take care of the Terminal cases.
    // The paper neglects to do that.
    u' o' (fun branch -> u (update_at_branch_descent o o' branch) branch - u o branch) tree

#r @"..\packages\FsCheck.3.0.0-alpha4\lib\net452\FsCheck.dll"
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
        if s > 0 then
            gen {
                let! (id : Infoset) = Gen.choose (0, infoset_sizes.Length-1)
                let infoset_size = infoset_sizes.[id]
                let! branches = Array.init infoset_size (fun _ -> loop (s/infoset_size)) |> Gen.sequenceToArr
                return Response(id,branches)
            }
        else gen_terminal
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
    static member Game = Arb.fromGen (gen_game 2 5 2)

Arb.register<MyGenerators>()

Arb.from<TreePolicies>.Generator
|> Gen.sample 1

let ``R=R'`` {tree=tree; policies=policies} =
    let (=?) a b = abs (a - b) <= 10.0 ** -7.0
    let o, o' = policies.[0], policies.[1]
    R o o' tree <= R' o o' tree

Check.Quick ``R=R'``