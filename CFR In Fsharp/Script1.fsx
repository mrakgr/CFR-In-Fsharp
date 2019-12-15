let polyIntersect is_poly intersect first rest = 
    assert (is_poly first = 1)
    assert (List.forall (fun x -> is_poly x = 1) rest)
    let r = List.fold intersect first rest
    assert (is_poly r = 1 + List.length rest)
    r

