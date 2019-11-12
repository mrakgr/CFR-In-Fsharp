#load "Core.fsx"
open Core
open FsCheck

// All the proof steps in more readable form.

let theorem_3 (TreePolicy(o_old,o_new,tree)) =
    let path = []
    // Full regret - eq 8
    // Player two always follows the old policy.
    // Throughout the paper the authors do a weird thing where instead of passing o_new to u directly, they instead carefully filter it so only the descendants
    // get added, but that is needless work due to the perfect recall property so it won't be done here.
    let R_full (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
        1.0 / float o_old.Length * o_max o_new (fun o_new -> o_sum o_old (fun o_old -> pi o_old path * (u o_new o_old tree - u o_old o_old tree)))
    
    relation (R_full o_old o_new [] tree) [
        // The actual full regret in the proof.
        // For the missing step between eq 8 and eq 9. It should be the left side of eq 9.
        let R_full' (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
            1.0 / float o_old.Length *
            action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> pi o_old path * (u (action_update o_new a tree) o_old tree - u o_old o_old tree))))

        // Lemma 5

        // The fact that the paper never got around to even stating this between eq 8 and eq 9 is its biggest ommision in my view.
        // What the following takes advantage of is that getting the maximum of a list is essentially always better or equal to 
        // getting some probabilistically weighted combination of its elements. In the context of regret calculation it is essential 
        // that perfect recall is maintained.

        // Otherwise what will happen is that dependencies will get introduced between the policy at the current node its child nodes.
        // If that happens it will no longer be true that taking the max of the pure strategies will give the optimal result and the following
        // test would not hold.

        // You can verify this by removing perfect recall in the `gen_tree` function.
        lte "eq 8.5" (R_full' o_old o_new [] tree) 

        // Note that pi o_old path * u o_old_a o_old tree = pi o_old path * pi o_old path' * u o_old o_old branch, hence the two quantities subtract to zero.
        eq "eq 9" (
            1.0 / float o_old.Length *
            action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
                let o_old_a = action_update o_old a tree
                pi o_old path * (u o_old_a o_old tree - u o_old o_old tree
                + sum_succ_a a tree (fun path' branch -> pi o_old_a path' * (u (action_update o_new a tree) o_old branch - u o_old o_old branch))
                ))))
            )

        // As the current player's action does not get added to path in succ_a, that means that pi o_old_a path' = pi o_old path'
        // Due to perfect recall u (action_update o_new a tree) o_old branch = u o_new o_old branch
        eq "eq 9 equivalence" (
            1.0 / float o_old.Length *
            action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
                pi o_old path * (u (action_update o_old a tree) o_old tree - u o_old o_old tree
                + sum_succ_a a tree (fun path' branch -> pi o_old path' * (u o_new o_old branch - u o_old o_old branch))
                ))))
            )

        // It is a simple split of the max.
        lte "eq 10" (
            1.0 / float o_old.Length *
            action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
                pi o_old path * (u (action_update o_old a tree) o_old tree - u o_old o_old tree)
                ))) +
            1.0 / float o_old.Length *
            action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
                pi o_old path * (sum_succ_a a tree (fun path' branch -> pi o_old path' * (u o_new o_old branch - u o_old o_old branch))
                ))))
            )

        // Immediate regret
        let R_imm (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
            1.0 / float o_old.Length *
            action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
                pi o_old path * (u (action_update o_old a tree) o_old tree - u o_old o_old tree)
                )))

        lte "eq 10 equivalence" (
            R_imm o_old o_new path tree +
            1.0 / float o_old.Length *
            action_max tree (fun a -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
                pi o_old path * (sum_succ_a a tree (fun path' branch -> pi o_old path' * (u o_new o_old branch - u o_old o_old branch))
                ))))
            )

        eq "eq 11" (
            R_imm o_old o_new path tree +
            1.0 / float o_old.Length *
            action_max tree (fun a -> o_max o_new (fun o_new -> sum_succ_a a tree (fun path' branch -> o_sum o_old (fun o_old -> 
                pi o_old (path' @ path) * (u o_new o_old branch - u o_old o_old branch)
                ))))
            )

        // Eq 12 has been skipped as I use the original definition of the full regret in eq 13.
        // max (fun a -> sum (fun b -> f a b)) <= sum (fun b -> max (fun a -> f a b))
        lte "eq 13" (
            R_imm o_old o_new path tree +
            1.0 / float o_old.Length *
            action_max tree (fun a -> sum_succ_a a tree (fun path' branch -> o_max o_new (fun o_new -> o_sum o_old (fun o_old -> 
                pi o_old (path' @ path) * (u o_new o_old branch - u o_old o_old branch)
                ))))
            )

        eq "eq 13 equivalence" (
            R_imm o_old o_new path tree +
            action_max tree (fun a -> sum_succ_a a tree (fun path' branch -> 
                R_full o_old o_new (path' @ path) branch
                ))
            )

        let R_full_split (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
            R_imm o_old o_new path tree + sum_succ tree (fun path' branch -> max 0.0 (R_full o_old o_new (path' @ path) branch))

        lte "eq 14" (R_full_split o_old o_new path tree)

        // Lemma 6
        
        // This one is different than in the paper
        
        lte "lemma 6 - 1" (
            R_imm o_old o_new path tree + sum_succ tree (fun path' branch -> max 0.0 (R_full_split o_old o_new (path' @ path) branch))
            )

        // Now it has already been established that 
        // R_full o_old o_new path tree <= R_full_split o_old o_new path tree
        // Hence it should hold that
        //    R_imm o_old o_new path tree + sum_succ tree (fun path' branch -> max 0.0 (R_full       o_old o_new (path' @ path) branch))
        // <= R_imm o_old o_new path tree + sum_succ tree (fun path' branch -> max 0.0 (R_full_split o_old o_new (path' @ path) branch))

        // Now the next part is a bit awkward as you cannot prove recursion directly using randomized testing. You could do this fully formally in Agda
        // but it if I picked that route I would be here forever.
        // Instead let me just illustrate how things should go.
        let rec R_full_split_rec (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
            R_imm o_old o_new path tree + sum_succ tree (fun path' branch -> max 0.0 (R_full_split_rec o_old o_new (path' @ path) branch))

        lte "lemma 6 - 2" (R_full_split_rec o_old o_new path tree)

        let rec R_imm_sum (o_old : Policy []) (o_new : Policy[]) path (tree : GameTree) = 
            max 0.0 (R_imm o_old o_new path tree) + sum_succ tree (fun path' branch -> R_imm_sum o_old o_new (path' @ path) branch)

        lte "theorem 3" (R_imm_sum o_old o_new path tree)
        // This (approximately) proves theorem 3.
        ]

Check.One({Config.Quick with MaxTest=10000}, theorem_3)