let error_bound_for_floats = 10.0 ** -7.0
let (=~) a b = abs (a - b) <= error_bound_for_floats
let (<=~) a b = a <= b + error_bound_for_floats
let (<~) a b = a < b + error_bound_for_floats
let (>=~) a b = a >= b - error_bound_for_floats
let (>~) a b = a > b - error_bound_for_floats

let prob_dist x = Array.forall ((<=) 0.0) x && Array.sum x =~ 1.0

let is_convex_set (l : float []) =
    if Array.length l < 2 then true
    else
        let rec loop f s i = if i < l.Length then let b, s = f s l.[i] in b && loop f s (i+1) else true
        let x = l.[1]
        let d = x - l.[0]
        let start op =
            loop (fun (d,x) x' ->
                let d' = x' - x
                let a = d' - d
                op a, (d',x')
                ) (d,x) 2

        start ((<=~) 0.0) || start ((>=~) 0.0)

is_convex_set [|0.0;0.5;0.7;0.9;1.0;1.1;1.15;1.17;1.18;1.0|]