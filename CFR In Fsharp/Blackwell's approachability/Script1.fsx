let error_bound_for_floats = 10.0 ** -7.0
let (=~) a b = abs (a - b) <= error_bound_for_floats

let prob_dist x = Array.forall ((<=) 0.0) x && Array.sum x =~ 1.0

let convex_set l x =
    prob_dist l