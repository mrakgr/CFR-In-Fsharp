#r @"..\..\packages\FsCheck.3.0.0-alpha4\lib\net452\FsCheck.dll"
open FsCheck

// Equalities and inequalities, transitive relation

let error_bound_for_floats = 10.0 ** -7.0
let (=~) a b = abs (a - b) <= error_bound_for_floats
let (<=~) a b = a <= b + error_bound_for_floats
let (<~) a b = a < b + error_bound_for_floats

let (.=) a b = a =~ b |@ sprintf "%f = %f" a b
let (.<=) a b = a <=~ b |@ sprintf "%f <= %f" a b
let (.<) a b = a <~ b |@ sprintf "%f < %f" a b

type Op = Eq of float | Lt of float | Lte of float | Label of Op * string

let rec relation s l = 
    let rec body x a = 
        match x with
        | Eq b -> a =~ b |@ sprintf "%f =~ %f is false" a b, b
        | Lte b -> a <=~ b |@ sprintf "%f <=~ %f is false" a b, b
        | Lt b -> a <~ b |@ sprintf "%f <~ %f is false" a b, b
        | Label (op, message) -> let prop, b = body op a in prop |@ message, b
            
    List.fold (fun (prop, a) x -> let prop', b = body x a in prop .&. prop', b) (true |@ "trivial", s) l
    |> fst

let eq label x = Label(Eq x, label)
let lte label x = Label(Lte x, label)
//let lt label x = Label(Lt x, label)

// Types

type Infoset = int
type Size = int
type Player = int 

type GameTree = // Chance nodes could be considered player nodes with both the opponent and current player policies being equal.
| Terminal of reward : float
| Response of id : Infoset * branches : GameTree []

type PolicyAtNode = float []
type Policy = Map<Infoset, PolicyAtNode>

// Testing

type TreePolicies = TreePolicy of o_old : Policy [] * o_new : Policy [] * tree : GameTree

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

/// One important consideration when generating the tree is to make sure that infosets do not repeat in the child nodes.
/// Hence it is necessary to keep track of parent's infosets in order to avoid selecting them.
/// The proofs will fail unless that is done.
let gen_tree : Gen<GameTree * Size []> = Gen.sized <| fun s -> gen {
    let infoset_sizes = ResizeArray()
    let rec response infoset_removed s =
        if s > 0 then
            gen {
                // Replace `infoset_removed` with `Set.empty` to generate trees without perfect recall.
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

let gen_game num_old num_new : Gen<TreePolicies> = gen {
    let! tree, infoset_sizes = gen_tree
    let! o_old = gen_policy infoset_sizes |> Gen.arrayOfLength num_old
    let! o_new = gen_policy infoset_sizes |> Gen.arrayOfLength num_new
    return TreePolicy(o_old, o_new, tree)
    }

type MyGenerators =
    static member Game = Arb.fromGen (gen_game 5 5)

Arb.register<MyGenerators>()

// Proof related functions

let action_max (tree : GameTree) next =
    match tree with
    | Terminal _ -> next -1
    | Response (id, branches) ->
        let rec loop s i = if i < branches.Length then loop (max s (next i)) (i+1) else s
        loop -infinity 0

let action_update o i tree =
    match tree with
    | Terminal _ -> o
    | Response (id, branches) -> 
        let a = Array.zeroCreate branches.Length
        a.[i] <- 1.0
        Map.add id a o

let inline u' (o : Policy) tree next = 
    match tree with
    | Terminal reward -> reward
    | Response (id, branches) -> Array.fold2 (fun s policy branch -> s + (if policy <> 0.0 then policy * next branch else 0.0)) 0.0 o.[id] branches

// Evaluates the first player, then the second, then loops back to first.
let rec u (o_one : Policy) (o_two : Policy) tree = u' o_one tree (fun branch -> u' o_two branch (u o_one o_two))
// How it would be if player two was the starter.
let rec u_two (o_one : Policy) (o_two : Policy) tree = u' o_two tree (fun branch -> u' o_one branch (u_two o_one o_two))

let o_max o next = Array.fold (fun s x -> max s (next x)) -infinity o
let o_sum o next = Array.fold (fun s x -> s + next x) 0.0 o

let inline on_branches next branches = Array.fold (fun (s, i) branch -> s + next i branch, i + 1) (0.0, 0) branches |> fst
/// Note that succ is intended to be used for regret calculations hence it returns 0.0 on terminal nodes.
let inline on_response next tree = match tree with Terminal _ -> 0.0 | Response (id, branches) -> next id branches

let inline succ' (tree : GameTree) next =
    on_response (fun id -> on_branches (fun i branch -> next [id, i] branch)) tree
let sum_succ (tree : GameTree) next =
    on_response (fun _ -> on_branches (fun _ branch -> succ' branch next)) tree
let sum_succ_a a (tree : GameTree) next =
    on_response (fun _ branches -> succ' branches.[a] next) tree

let pi (o : Policy) path = List.fold (fun s (id, i) -> s * o.[id].[i]) 1.0 path
