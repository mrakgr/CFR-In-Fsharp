let g x = failwith ""

let f<'a,'b,'c,'d> (x: 'a) :'d =
    g (g (g x : 'b) : 'c)
    
