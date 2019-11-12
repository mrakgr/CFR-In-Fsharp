#load "Core.fsx"
open Core

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
let succ (tree : GameTree) next =
    on_response (fun _ -> on_branches (fun _ branch -> succ' branch next)) tree
let succ_a a (tree : GameTree) next =
    on_response (fun _ branches -> succ' branches.[a] next) tree

open FsCheck
let (=?) a b = a =? b |@ sprintf "%f = %f" a b
let (<=?) a b = a <=? b |@ sprintf "%f <= %f" a b

let pi (o : Policy) path = List.fold (fun s (id, i) -> s * o.[id].[i]) 1.0 path

// Eq 8
// Player two always follows the old policy.
// Throughout the paper the authors do a weird thing where instead of passing o_new to u directly, they instead carefully filter it so only the descendants
// get added, but that is needless work due to the perfect recall property so it won't be done.
let R_full (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    1.0 / float o_old.Length * o_max o_new (fun o_new -> o_sum o_old (fun o_old -> pi o_old path * (u o_new o_old tree - u o_old o_old tree)))

// For the missing step between eq 8 and eq 9. It should be the left side of eq 9.
let R_full' (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    1.0 / float o_old.Length *
    action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> pi o_old path * (u (action_update o_new a tree) o_old tree - u o_old o_old tree))))

// The fact that the paper never got around to even stating this between eq 8 and eq 9 is its biggest ommision in my view.
// What the following takes advantage of is that getting the maximum of a list is essentially always better or equal to 
// getting some probabilistically weighted combination of its elements. In the context of regret calculation it is essential 
// that perfect recall is maintained.

// Otherwise what will happen is that dependencies will get introduced between the policy at the current node its child nodes.
// If that happens it will no longer be true that taking the max of the pure strategies will give the optimal result and the following
// test would not hold.

// You can verify this by removing perfect recall in the `gen_tree` function.

//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full o_old o_new [] tree <=? R_full' o_old o_new [] tree
//    )

// Right side of eq 9
// As the current player's action does not get added to path in succ_a, that means that pi o_old_a path' = pi o_old path'
// Due to perfect recall u (action_update o_new a tree) o_old branch = u o_new o_old branch
// Note that pi o_old path * u o_old_a o_old tree = pi o_old path * pi o_old path' * u o_old o_old branch, hence the two quantities subtract to zero.
let R_full'' (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    1.0 / float o_old.Length *
    action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
        let o_old_a = action_update o_old a tree
        pi o_old path * (u o_old_a o_old tree - u o_old o_old tree
        + succ_a a tree (fun path' branch -> pi o_old_a path' * (u (action_update o_new a tree) o_old branch - u o_old o_old branch))
        ))))

//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full' o_old o_new [] tree =? R_full'' o_old o_new [] tree
//    )

let R_full''_alt (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    1.0 / float o_old.Length *
    action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
        pi o_old path * (u (action_update o_old a tree) o_old tree - u o_old o_old tree
        + succ_a a tree (fun path' branch -> pi o_old path' * (u o_new o_old branch - u o_old o_old branch))
        ))))

Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
    R_full'' o_old o_new [] tree =? R_full''_alt o_old o_new [] tree
    )

let R_imm (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    1.0 / float o_old.Length *
    action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
        pi o_old path * (u (action_update o_old a tree) o_old tree - u o_old o_old tree)
        )))

let succ_R_full (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    1.0 / float o_old.Length *
    action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
        pi o_old path * (succ_a a tree (fun path' branch -> pi o_old path' * (u o_new o_old branch - u o_old o_old branch))
        ))))

// Right side of eq 10
// It is a simple split of the max.
let R_full''' (o_old : Policy []) (o_new : Policy[]) pi (tree : GameTree) = R_imm o_old o_new pi tree + succ_R_full o_old o_new pi tree
    
//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full'' o_old o_new [] tree <=? R_full''' o_old o_new [] tree
//    )

let R_full_succ (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    1.0 / float o_old.Length *
    action_max tree (fun a -> o_max o_new (fun o_new -> succ_a a tree (fun path' branch -> o_sum o_old (fun o_old -> 
        pi o_old (path' @ path) * (u o_new o_old branch - u o_old o_old branch)
        ))))

//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    succ_R_full o_old o_new [] tree =? R_full_succ o_old o_new [] tree
//    )

// Equivalent to R_full_succ with the succ_a lifted outside the maximum.
let R_full_succ' (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    action_max tree (fun a -> succ_a a tree (fun path' branch -> 
        R_full o_old o_new (path' @ path) branch
        ))

//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full_succ o_old o_new [] tree <=? R_full_succ' o_old o_new [] tree
//    )

//// Right side of eq 11
//// Equal to R_full'''
//let R_full'''' (o_old : Policy []) (o_new : Policy[]) pi (tree : GameTree) = R_imm o_old o_new pi tree + R_full_succ o_old o_new pi tree

//let R_full_succ' (o_old : Policy []) (o_new : Policy[]) pi (tree : GameTree) = 
//    action_max tree (fun a -> 1.0 / float o_old.Length * o_sum o_old (fun o_old -> 
//        let o_old_a = action_update o_old a tree
//        succ_a o_old_a tree (fun pi' branch -> R_full [|o_old|] o_new (pi * pi') branch)
//        ))