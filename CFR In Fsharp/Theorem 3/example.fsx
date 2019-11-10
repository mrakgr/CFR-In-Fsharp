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

let R_imm (o' : Policy) (o : Policy) (tree : GameTree) = 
    let o' = update_at_branch_current o o' tree
    max 0.0 (u o' tree - u o tree)

let rec R_imm_sum (o' : Policy) (o : Policy) (tree : GameTree) =
    match tree with
    | Terminal _ -> 0.0 // This check is to avoid double counting the Terminal nodes due to the recursion. It is not an issue in the eq 9 test.
    | Response (_, branches) -> 
        // As it is assumed that the opponent only has one action in every node, the CFR reach probabilities are all 1 and play no role.
        R_imm o' o tree + Array.fold (fun s branch -> s + R_imm_sum o' o branch) 0.0 branches

open FsCheck

let ``R_full<=R_imm_sum'`` ({tree=tree; policies=policies} : TreePolicies) =
    let o, o' = policies.[0], policies.[1]
    let left = R_full o' o tree
    let right = R_imm_sum o' o tree
    left <= right |@ sprintf "%f <= %f" left right

// Fails
Check.One({Config.Quick with MaxTest=100000}, ``R_full<=R_imm_sum'``)
