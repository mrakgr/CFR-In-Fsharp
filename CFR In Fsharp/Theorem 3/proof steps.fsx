#load "Core.fsx"
open Core
open FsCheck
let (=?) a b = a =? b |@ sprintf "%f = %f" a b
let (<=?) a b = a <=? b |@ sprintf "%f <= %f" a b

// Lemma 5

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

// Eq 8.5
//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full o_old o_new [] tree <=? R_full' o_old o_new [] tree
//    )

// Right side of eq 9
// Note that pi o_old path * u o_old_a o_old tree = pi o_old path * pi o_old path' * u o_old o_old branch, hence the two quantities subtract to zero.
let R_full'' (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    1.0 / float o_old.Length *
    action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
        let o_old_a = action_update o_old a tree
        pi o_old path * (u o_old_a o_old tree - u o_old o_old tree
        + sum_succ_a a tree (fun path' branch -> pi o_old_a path' * (u (action_update o_new a tree) o_old branch - u o_old o_old branch))
        ))))

// Eq 9
//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full' o_old o_new [] tree =? R_full'' o_old o_new [] tree
//    )

// As the current player's action does not get added to path in succ_a, that means that pi o_old_a path' = pi o_old path'
// Due to perfect recall u (action_update o_new a tree) o_old branch = u o_new o_old branch
let R_full''_alt (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    1.0 / float o_old.Length *
    action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
        pi o_old path * (u (action_update o_old a tree) o_old tree - u o_old o_old tree
        + sum_succ_a a tree (fun path' branch -> pi o_old path' * (u o_new o_old branch - u o_old o_old branch))
        ))))

//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full'' o_old o_new [] tree =? R_full''_alt o_old o_new [] tree
//    )

let R_imm (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    1.0 / float o_old.Length *
    action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
        pi o_old path * (u (action_update o_old a tree) o_old tree - u o_old o_old tree)
        )))

let succ_R_full (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    1.0 / float o_old.Length *
    action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
        pi o_old path * (sum_succ_a a tree (fun path' branch -> pi o_old path' * (u o_new o_old branch - u o_old o_old branch))
        ))))

// Right side of eq 10
// It is a simple split of the max.
let R_full''' (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = R_imm o_old o_new path tree + succ_R_full o_old o_new path tree
    
// Eq 10
//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full'' o_old o_new [] tree <=? R_full''' o_old o_new [] tree
//    )

let R_full_succ (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    1.0 / float o_old.Length *
    action_max tree (fun a -> o_max o_new (fun o_new -> sum_succ_a a tree (fun path' branch -> o_sum o_old (fun o_old -> 
        pi o_old (path' @ path) * (u o_new o_old branch - u o_old o_old branch)
        ))))

//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    succ_R_full o_old o_new [] tree =? R_full_succ o_old o_new [] tree
//    )

// Right side of eq 11
let R_full'''' (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = R_imm o_old o_new path tree + R_full_succ o_old o_new path tree

// Eq 11
//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full''' o_old o_new [] tree =? R_full'''' o_old o_new [] tree
//    )

// Eq 12 has been skipped.

// Equivalent to R_full_succ with the sum_succ_a lifted outside the maximum.
let R_full_succ' (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    action_max tree (fun a -> sum_succ_a a tree (fun path' branch -> 
        R_full o_old o_new (path' @ path) branch
        ))

// max (fun a -> sum (fun b -> f a b)) <= sum (fun b -> max (fun a -> f a b))
//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full_succ o_old o_new [] tree <=? R_full_succ' o_old o_new [] tree
//    )

// Right side of eq 13
// Unlike in the paper, I use the original definition of R_full here rather than adding an empty max for no reason.
let R_full''''' (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = R_imm o_old o_new path tree + R_full_succ' o_old o_new path tree

// Eq 13
//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full'''' o_old o_new [] tree <=? R_full''''' o_old o_new [] tree
//    )

let R_full_succ'' (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    sum_succ tree (fun path' branch -> max 0.0 (R_full o_old o_new (path' @ path) branch))

// reduce max l <= sum (map (max 0.0) l)
//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full_succ' o_old o_new [] tree <=? R_full_succ'' o_old o_new [] tree
//    )

// Right side of eq 14
let R_full'''''' (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = R_imm o_old o_new path tree + R_full_succ'' o_old o_new path tree

// Eq 14
//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full''''' o_old o_new [] tree <=? R_full'''''' o_old o_new [] tree
//    )

// Lemma 6

// This one I am going to do differnetly than in the paper.

let R_full_split (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    R_imm o_old o_new path tree + sum_succ tree (fun path' branch -> max 0.0 (R_full o_old o_new (path' @ path) branch))

let R_full_split' (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    R_imm o_old o_new path tree + sum_succ tree (fun path' branch -> max 0.0 (R_full_split o_old o_new (path' @ path) branch))

//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full'''''' o_old o_new [] tree =? R_full_split o_old o_new [] tree
//    )

// Now it has already been established that 
// R_full o_old o_new path tree <= R_full_split o_old o_new path tree
// Hence it should hold that
//    R_imm o_old o_new path tree + sum_succ tree (fun path' branch -> max 0.0 (R_full       o_old o_new (path' @ path) branch))
// <= R_imm o_old o_new path tree + sum_succ tree (fun path' branch -> max 0.0 (R_full_split o_old o_new (path' @ path) branch))

//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full_split o_old o_new [] tree 
//    <=? R_full_split' o_old o_new [] tree
//    )

// Now the next part is a bit awkward as you cannot prove recursion directly using randomized testing. You could do this fully formally in Agda
// but it if I picked that route I would be here forever.
// Instead let me just illustrate how things should go.
let rec R_full_split_rec (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    R_imm o_old o_new path tree + sum_succ tree (fun path' branch -> max 0.0 (R_full_split_rec o_old o_new (path' @ path) branch))

//Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
//    R_full_split' o_old o_new [] tree
//    <=? R_full_split_rec o_old o_new [] tree
//    )

let rec R_imm_sum (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
    max 0.0 (R_imm o_old o_new path tree) + sum_succ tree (fun path' branch -> R_imm_sum o_old o_new (path' @ path) branch)

Check.One({Config.Quick with MaxTest=10000}, fun (TreePolicy(o_old,o_new,tree)) -> 
    R_full_split_rec o_old o_new [] tree
    <=? R_imm_sum o_old o_new [] tree
    )

/// This (approximately) proves theorem 3.