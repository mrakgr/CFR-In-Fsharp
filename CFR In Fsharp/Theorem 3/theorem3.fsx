#load "Core.fsx"
open Core

let u' (o : Policy) f = function
    | Terminal reward -> reward
    | Response (id, branches) -> Array.fold2 (fun s policy branch -> s + f policy branch) 0.0 o.[id] branches

let rec u (o : Policy) tree = u' o (fun policy branch -> policy * u o branch) tree

let R_full (o' : Policy) (o : Policy) (tree : GameTree) = 
    let l = u o' tree 
    let r = u o tree
    l - r

let update_at_branch_current cur next = function
    | Terminal _ -> cur
    | Response (id, _) -> Map.add id (Map.find id next) cur

let R_imm (o' : Policy) (o : Policy) (tree : GameTree) = 
    let o' = update_at_branch_current o o' tree
    let l = u o' tree
    let r = u o tree
    let res = max 0.0 (l - r)
    printfn "tree=%A" tree
    printfn "%A\n%A\nmax 0.0 (l - r)=%f" (o', l) (o, r) res
    res

let rec R_imm_sum (o' : Policy) (o : Policy) (tree : GameTree) =
    match tree with
    | Terminal _ -> 0.0 // This check is to avoid double counting the Terminal nodes due to the recursion. It is not an issue in the eq 9 test.
    | Response _ -> 
        // No multiplication by the player probabilities. It does not matter whether o' or o is passed to u'.
        // As it is assumed that the opponent only has one action in every node, the CFR reach probabilities are all 1 and play no role.
        R_imm o' o tree + u' o' (fun _ branch -> R_imm_sum o' o branch) tree

open FsCheck

let ``R_full<=R_imm_sum'`` ({tree=tree; policies=policies} : TreePolicies) =
    let o, o' = policies.[0], policies.[1]
    let left = R_full o' o tree
    let right = R_imm_sum o' o tree
    left <= right |@ sprintf "Failure. %f <> %f. Error bound for floats is %f." left right error_bound_for_floats

// Fails
//Check.One({Config.Quick with MaxTest=100000}, ``R_full<=R_imm_sum'``)

// Surprisingly it seems that theorem 3 is false as well.
// Here is a counter example.

//Falsifiable, after 6543 tests (0 shrinks) (17947101256372067428,14787371683992192641)
//Last step was invoked with size of 7 and seed of (543175987540267980,12028313537534174055):
//Label of failing property: Failure. 8.300594 <> 1.965112. Error bound for floats is 0.000000.
//Original:
//{ policies =
//            [|map
//                [(0, [|0.005; 0.99091; 0.00409|]); (1, [|0.91659; 0.08341|]);
//                 (2, [|0.17351; 0.23036; 0.33814; 0.25799|]);
//                 (3, [|0.81159; 0.18841|]);
//                 (4, [|0.05401; 0.0144; 0.88171; 0.04988|])];
//              map
//                [(0, [|0.30333; 0.54771; 0.14896|]); (1, [|0.1455; 0.8545|]);
//                 (2, [|0.03393; 0.39449; 0.52965; 0.04193|]);
//                 (3, [|0.15721; 0.84279|]);
//                 (4, [|0.02714; 0.30085; 0.09428; 0.57773|])]|]
//  tree =
//        Response
//          (1,
//           [|Terminal -6.3;
//             Response
//               (3,[|Response (1,[|Terminal 8.5; Terminal -7.1|]); Terminal 6.5|])|])
//  infoset_sizes = [|3; 2; 4; 2; 4|] }

let f ({tree=tree; policies=policies} : TreePolicies) =
    let o, o' = policies.[0], policies.[1]
    let left = R_full o' o tree
    let right = R_imm_sum o' o tree
    left, right

let example =
    { policies =
                [|Map
                    [(0, [|1.0; 0.0|]);
                     (1, [|1.0; 0.0|]);
                     ];
                  Map
                    [(0, [|0.0; 1.0|]);
                     (1, [|0.0; 1.0|]);
                     ]|]
      tree =
            Response
              (0,
               [|Terminal -10.0;
                 Response
                   (1,[|Response (0,[|Terminal 10.0; Terminal -10.0|]); Terminal 10.0|])|])
      infoset_sizes = [|2; 2|] }

f example

