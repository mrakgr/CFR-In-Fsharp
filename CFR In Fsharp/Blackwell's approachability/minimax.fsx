let error_bound_for_floats = 10.0 ** -7.0
let (=~) a b = abs (a - b) <= error_bound_for_floats

let prob_dist x = Array.forall ((<=) 0.0) x && Array.sum x =~ 1.0
let size x = Array.length x
let size2 M = Array2D.length1 M, Array2D.length2 M
let forall (r,s) f = 
    let rec loop1 i =
        let rec loop2 j = if j < s then f i j && loop2 (j+1) else loop1 (i+1)
        if i < r then loop2 0 else true
    loop1 0

let sum l f = 
    let rec loop s i = if i < l then loop (s + f i) (i+1) else s
    loop 0.0 0

// The main difference between the definition here and the one at the start of the paper is that I replaced the existentials with a generating function.
// See `https://book.simply-logical.space/part_i.html#the_relation_between_clausal_logic_and_predicate_logic` for examples of Skolemization.
let theorem_minimax gen M = 
    let p, q = gen M 
    prob_dist p && prob_dist q && 
    forall (size2 M) (fun i j -> sum (size p) (fun i -> p.[i] * M.[i,j]) >= sum (size q) (fun j -> q.[j] * M.[i,j]))

// I do not actually know how to construct the generating function, but the property should suffice for testing should it be necessary.
    