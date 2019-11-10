#load "Core.fsx"
open Core

let action_at i (o : Policy) (id : Infoset) =
    let a = Array.zeroCreate o.[id].Length
    a.[i] <- 1.0
    Map.add id a o

let action_max (o : Policy) (id : Infoset) next =
    let len = o.[id].Length
    let rec loop s i =
        if i < len then
            let a = Array.zeroCreate len
            a.[i] <- 1.0
            loop (max s (next (Map.add id a o))) (i+1)
        else s
    loop -infinity 0

let inline u' (o : Policy) tree next = 
    match tree with
    | Terminal reward -> reward
    | Response (id, branches) -> Array.fold2 (fun s policy branch -> s + (if policy <> 0.0 then policy * next branch else 0.0)) 0.0 o.[id] branches

// Evaluates the first player, then the second, then loops back to first.
let rec u (o_one : Policy) (o_two : Policy) tree = u' o_one tree (fun branch -> u' o_two branch (u o_one o_two))
// How it would be if player two was the starter.
let rec u_two (o_one : Policy) (o_two : Policy) tree = u' o_two tree (fun branch -> u' o_one branch (u_two o_one o_two))

/// Player two always follows the old policy.
let R_full (o_old : Policy) (o_new : Policy) (tree : GameTree) = u o_new o_old tree - u o_old o_old tree

let R_imm (o : Policy) (tree : GameTree) = 
    match tree with
    | Terminal _ -> 0.0
    | Response (id, _) -> action_max o id (fun o' -> u o' o tree - u o o tree)

let succ (o : Policy) (branches : GameTree []) (next : GameTree -> float) =
    let inline on_branches next branches = Array.fold (fun (s, i) branch -> s + next i branch, i + 1) (0.0, 0) branches |> fst
    let inline on_response next tree = match tree with Terminal x -> x | Response (id, branches) -> next id branches
    on_branches (fun _ -> on_response (fun id -> let o = o.[id] in on_branches (fun i branch -> o.[i] * next branch))) branches

let rec R_imm_sum (o : Policy) (tree : GameTree) =
    match tree with
    | Terminal _ -> 0.0
    | Response (_, branches) -> R_imm o tree + succ o branches (R_imm_sum o)

open FsCheck

let ``R_full<=R_imm_sum'`` ({tree=tree; policies=policies} : TreePolicies) =
    let o, o' = policies.[0], policies.[1]
    let left = R_full o' o tree
    let right = R_imm_sum o' o tree
    left <= right |@ sprintf "%f <= %f" left right

// Fails
Check.One({Config.Quick with MaxTest=10000}, ``R_full<=R_imm_sum'``)

