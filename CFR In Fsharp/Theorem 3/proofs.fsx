#load "Core.fsx"
open Core

let action_max (tree : GameTree) (next : PolicyAtNode -> float) =
    match tree with
    | Terminal _ -> next [||]
    | Response (id, branches) ->
        let body i = 
            let a = Array.zeroCreate branches.Length
            a.[i] <- 1.0
            next a
        let rec loop s i = if i < branches.Length then loop (max s (body i)) (i+1) else s
        loop (body 0) 1

let action_update o a tree =
    match tree with
    | Terminal _ -> o
    | Response (id, branches) -> Map.add id a o

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
let inline on_response next tree = match tree with Terminal x -> x | Response (id, branches) -> next id branches

let inline succ' (o : Policy) (tree : GameTree) (next : GameTree -> float) =
    on_response (fun id -> let o = o.[id] in on_branches (fun i branch -> o.[i] * next branch)) tree
let succ (o : Policy) (tree : GameTree) (next : GameTree -> float) =
    on_response (fun _ -> on_branches (fun _ branch -> succ' o branch next)) tree
let succ_a (o : Policy) (tree : GameTree) (next : GameTree -> float) =
    on_response (fun id -> let o' = o.[id] in on_branches (fun i branch -> let o' = o'.[i] in if o' <> 0.0 then o' * succ' o branch next else 0.0)) tree

open FsCheck

// Eq 8
// Player two always follows the old policy.
let R_full (o_old : Policy []) (o_new : Policy[]) (tree : GameTree) = 
    1.0 / float o_old.Length * o_max o_new (fun o_new -> o_sum o_old (fun o_old -> u o_new o_old tree - u o_old o_old tree))

// For the missing step between eq 8 and eq 9. It should be the left side of eq 9.
let R_full' (o_old : Policy []) (o_new : Policy[]) (tree : GameTree) = 
    1.0 / float o_old.Length *
    action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> u (action_update o_new a tree) o_old tree - u o_old o_old tree)))

// The fact that the paper never got around to even stating this between eq 8 and eq 9 is its biggest ommision in my view.
// What the following takes advantage of is that getting the maximum of a list is essentially always better or equal to 
// getting some probabilistically weighted combination of its elements. In the context of regret calculation it is essential 
// that perfect recall is maintained.

// Otherwise what will happen is that dependencies will get introduced between the policy at the current node its child nodes.
// If that happens it will no longer be true that taking the max of the pure strategies will give the optimal result and the following
// test would not hold.

// You can verify this by removing perfect recall in the `gen_tree` function.
let ``R_full<=R_full'`` ({tree=tree; policies_old=policies_old; policies_new=policies_new} : TreePolicies) =
    let left = R_full policies_old policies_new tree
    let right = R_full' policies_old policies_new tree
    left <=? right |@ sprintf "%f <= %f" left right

//Check.One({Config.Quick with MaxTest=10000}, ``R_full<=R_full'``)

// Right side of eq 9
// One of the errors the paper that has been fixed here is that succ is not really distributive due to the presence of terminal nodes.
// Note that `u o_old_a o_old tree` and `succ_a o_old_a tree (u o_old o_old)` are the same quantity and sum to zero.
let R_full'' (o_old : Policy []) (o_new : Policy[]) (tree : GameTree) = 
    1.0 / float o_old.Length *
    action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
        let o_old_a = action_update o_old a tree
        u o_old_a o_old tree - u o_old o_old tree
        + succ_a o_old_a tree (u (action_update o_new a tree) o_old)
        - succ_a o_old_a tree (u o_old o_old)
        )))

let ``R_full'=R_full''`` ({tree=tree; policies_old=policies_old; policies_new=policies_new} : TreePolicies) =
    let left = R_full' policies_old policies_new tree
    let right = R_full'' policies_old policies_new tree
    left =? right |@ sprintf "%f = %f" left right

//Check.One({Config.Quick with MaxTest=10000}, ``R_full'=R_full''``)

// Right side of eq 10
// It is a simple split of the max.
let R_full''' (o_old : Policy []) (o_new : Policy[]) (tree : GameTree) = 
    let l = 
        action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
            let o_old_a = action_update o_old a tree
            u o_old_a o_old tree - u o_old o_old tree
            )))
    let r = 
        action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
            let o_old_a = action_update o_old a tree
            succ_a o_old_a tree (u (action_update o_new a tree) o_old)
            - succ_a o_old_a tree (u o_old o_old)
            )))

    1.0 / float o_old.Length * (l + r)
    
let ``R_full''<=R_full'''`` ({tree=tree; policies_old=policies_old; policies_new=policies_new} : TreePolicies) =
    let left = R_full'' policies_old policies_new tree
    let right = R_full''' policies_old policies_new tree
    left <=? right |@ sprintf "%f <= %f" left right

//Check.One({Config.Quick with MaxTest=10000}, ``R_full''<=R_full'''``)