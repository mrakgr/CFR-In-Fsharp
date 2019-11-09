let inline gap_empty size next i = if i < size then i else size + next (i - size)
let inline gap_one next i = 1 + next i

//let rec loop (x,l) i =
//    match l with
//    | x' :: xs -> gap_empty (x' - x - 1) (gap_one (loop (x', xs))) i
//    | [] -> i

let loop l i =
    assert (Array.sort l = l)
    let rec loop x l_i i =
        if l_i < Array.length l then
            let x' = l.[l_i]
            gap_empty (x' - x - 1) (gap_one (loop x' (l_i+1))) i
        else
            i
    loop -1 0 i

let loop' l = Array.foldBack (fun x' next x -> gap_empty (x' - x - 1) (gap_one (next x'))) l (fun x' i -> i) -1

let loop'' l i = 
    let c, next = Array.foldBack (fun x' (c, next) -> c+1, fun x -> gap_empty (x' - x - 1) (gap_one (next x'))) l (0, (fun x' i -> i))
    c, next -1 i

loop'' [|0;4;5;6|] 4

//let pick_ith i (avail : _ []) (rem : Set<int>) =
//    let rem = Set.toArray rem
//    assert (rem.Length <= avail.Length)
//    assert (i <= rem.Length)
//    let i = i - rem_count
    
//    let rec loop k rem_index =
//        if rem.[rem_index] = k then
            