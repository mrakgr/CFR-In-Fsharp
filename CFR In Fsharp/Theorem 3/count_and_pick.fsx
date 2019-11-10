#r @"..\..\packages\FsCheck.3.0.0-alpha4\lib\net452\FsCheck.dll"
open FsCheck

let inline gap_empty size next i = if i < size then i else size + next (i - size)
let inline gap_one next i = 1 + next i

let rec loop_list (x,l) i =
    match l with
    | x' :: xs -> gap_empty (x' - x - 1) (gap_one (loop_list (x', xs))) i
    | [] -> i

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

/// Picks the ith index not in l.
let count_and_pick (l : Set<int>) =
    assert (Set.forall (fun x -> x >= 0) l)
    let c, next = Set.foldBack (fun x' (c, next) -> c+1, fun x i -> gap_empty (x' - x - 1) (gap_one (next x')) i) l (0, (fun x' i -> i))
    c, next -1

type RemSet = RemSet of Set<int> * int * int
let gen_remset = Gen.sized <| fun s -> 
    gen {
        //printfn "s is %i" s
        let! l = Gen.choose(0,s-1) |> Gen.arrayOfLength s |> Gen.map Set
        let! c = Gen.choose(0,s-l.Count-1)
        return RemSet(l,s,c)
    }


//Gen.sampleWithSize 10 5 gen_remset

type MyTypes =
    static member MakeRemSet = Arb.fromGen gen_remset

Arb.register<MyTypes>()

let ``removed not in set`` (RemSet (l, s, c)) =
    let l_count, pick_ith = count_and_pick l
    let i = pick_ith c
    l_count < s ==> lazy (Set.contains i l = false && i < s && l_count = l.Count)

Check.One({Config.Default with MaxTest=1000}, ``removed not in set``)