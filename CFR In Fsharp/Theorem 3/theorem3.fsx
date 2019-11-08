#load "Core.fsx"
open Core

let u' (o : Policy) f = function
    | Terminal reward -> reward
    | Response (id, branches) -> Array.fold2 (fun s policy branch -> s + f policy branch) 0.0 o.[id] branches

let rec u (o : Policy) tree = u' o (fun policy branch -> policy * u o branch) tree

let R_full (o' : Policy) (o : Policy) (tree : GameTree) = u o' tree - u o tree

let update_at_branch_current cur next = function
    | Terminal _ -> cur
    | Response (id, _) -> Map.add id (Map.find id next) cur

let R_imm (o' : Policy) (o : Policy) (tree : GameTree) = u (update_at_branch_current o o' tree) tree - u o tree |> max 0.0

let rec R_imm_sum (o' : Policy) (o : Policy) (tree : GameTree) =
    R_imm o' o tree +
    // No multiplication by the player probabilities. It does not matter whether o' or o is passed to u'.
    u' o' (fun _ branch -> R_imm_sum o' o tree) tree

open FsCheck

let ``R_full<=R_imm_sum'`` ({tree=tree; policies=policies} : TreePolicies) =
    let o, o' = policies.[0], policies.[1]
    let left = R_full o' o tree
    let right = R_imm_sum o' o tree
    // Tests for equality and prints an error if the property fails
    left =? right |@ sprintf "Failure. %f <> %f. Error bound for floats is %f." left right error_bound_for_floats

// Fails.
Check.Quick ``R=R'``