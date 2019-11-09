let pick_ith i (avail : _ []) (rem : Set<int>) =
    let rem = Set.toArray rem
    assert (rem.Length <= avail.Length)
    assert (i <= rem.Length)
    let i = i - rem_count
    
    let rec loop k rem_index =
        if rem.[rem_index] = k then
            