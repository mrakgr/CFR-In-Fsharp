// Tests for `A Simple Adaptive Procedure Leading To Correlated Equilibrium` by Sergiu Hart and Andreu Mas-Colell

let error_bound_for_floats = 10.0 ** -7.0
let (=~) a b = abs (a - b) <= error_bound_for_floats

type Strategy = int32
type Player = int32
type Players = int32

type Game = {
    // Fin x = 0 <= _ < x
    // Pos = 0 < _
    N : Players // Pos
    S : Player -> Strategy // Fin N -> Pos
    u : Player -> (Player -> Strategy) -> float // Fin N -> ((i : Fin N) -> Fin (S i)) -> NormalFloat
    }

let fold f state (g : Game) = 
    let s = Array.zeroCreate g.N
    let rec loop1 state player = 
        let rec loop2 state strategy = 
            if strategy < (g.S player) then s.[player] <- strategy; loop2 (loop1 state (player+1)) (strategy+1)
            else state
        if player < g.N then loop2 state 0 else f state (fun i -> s.[i])
    loop1 state 0

let forall (g : Game) f = fold (fun s x -> s && f x) true g
let sum (g : Game) f = fold (fun s x -> s + f x) 0.0 g

let is_normal_float r = (System.Double.IsInfinity r || System.Double.IsNaN r) = false

let Game_WF (g : Game) =
    let range from near_to f = 
        let rec loop i = if i < near_to then f i && loop (i + 1) else true
        loop from
    0 < g.N
    && range 0 g.N (fun player -> 0 < g.S player)
    && range 0 g.N (fun player -> forall g (fun strategies -> is_normal_float (g.u player strategies)))

let psi_WF g psi = forall g (fun s -> 0.0 <= psi s) && sum g (fun s -> psi s) =~ 1.0

// Similar to the definition of the correlated equilibrium from the paper, except it passes the arguments in proper order to u.
let coreq e g psi i j k = sum g (fun s -> if s i = j then psi s * (g.u i (fun i' -> if i = i' then k else s i') + g.u i s) else 0.0) <= e