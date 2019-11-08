// Intended to test eq 9 from the `Regret Minimization in Games with Incomplete Information` paper with some simplifying assumptions.
// * Chance nodes are not there.
// * T is 1.
// * Policy is not split into actions at current node and everything else.
// * Not maxing over multiple policies - only two are considered.
// * Only a single player is considered. This is equivalent to the other player having nodes with only a single action.

// All of the above are simplifications of the original definitions and could easily be added. But if the subset does not work, then
// the full proof won't either.

#load "Core.fsx"
open Core

let u' (o : Policy) f = function
    | Terminal reward -> reward
    | Response (id, branches) -> Array.fold2 (fun s policy branch -> s + f policy branch) 0.0 o.[id] branches

let rec u (o : Policy) tree = u' o (fun policy branch -> policy * u o branch) tree

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
    /// According to definition of succ which only considers opponent reach probabilities, 
    /// I skip multipling by current player reach probabilities.
    u' o (fun _ branch -> u (update_at_branch_descent o o' branch) branch - u o branch) tree

open FsCheck

let ``R=R'`` ({tree=tree; policies=policies} : TreePolicies) =
    let o, o' = policies.[0], policies.[1]
    let left = R o o' tree
    let right = R' o o' tree
    // Tests for equality and prints an error if the property fails
    left =? right |@ sprintf "Failure. %f <> %f. Error bound for floats is %f." left right error_bound_for_floats

// Fails.
Check.Quick ``R=R'``