﻿// Tests for `A Simple Adaptive Procedure Leading To Correlated Equilibrium` by Sergiu Hart and Andreu Mas-Colell

let error_bound_for_floats = 10.0 ** -7.0
let (=~) a b = abs (a - b) <= error_bound_for_floats

type Strategy = int
type Player = int
type NumPlayers = int
type NumStrategies = int
type NumTime = int
type Time = int

type Game = {
    // Fin x = 0 <= _ < x
    // Pos = 0 < _
    N : NumPlayers // Pos
    S : Player -> NumStrategies // Fin N -> Pos
    u : Player -> (Player -> Strategy) -> float // Fin N -> ((i : Fin N) -> Fin (S i)) -> NormalFloat
    T : NumTime // 0 <= _
    h : Time -> Player -> Strategy // (i : Fin T) -> Fin N -> Fin (S i)
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
    && 0 <= g.T
    && range 0 g.T (fun time -> range 0 g.N (fun player -> 0 <= g.h time player && g.h time player < g.S player))

let psi_WF g psi = forall g (fun s -> 0.0 <= psi s) && sum g (fun s -> psi s) =~ 1.0

// Similar to the definition of the correlated equilibrium from the paper, except it passes the arguments in proper order to u.
let coreq e g psi i j k = sum g (fun s -> if s i = j then psi s * (g.u i (fun i' -> if i = i' then k else s i') + g.u i s) else 0.0) <= e

// 2.1a
let W g i t j k = if g.h t i = j then g.u i (fun i' -> if i = i' then k else g.h t i') else g.u i (g.h t)

let sum_time t f =
    let rec loop s (i : Time) = if i < t then loop (s + f i) (i+1) else s
    loop 0.0 0

// 2.1b
let D' g t i j k = 1.0 / float t * sum_time t (fun t -> W g i t j k) - 1.0 / float t * sum_time t (fun t -> g.u i (g.h t))
let D g t i j k = 1.0 / float t * sum_time t (fun t -> if g.h t i = j then g.u i (fun i' -> if i = i' then k else g.h t i') - g.u i (g.h t) else 0.0)

// This has to hold.
let D_eq g t i j k = D' t g i j k = D t g i j k

// 2.1c
let R g t i j k = max 0.0 (D g t i j k)

let fold' f state player (g : Game) = 
    let rec loop2 state strategy = 
        if strategy < (g.S player) then loop2 (f state strategy) (strategy+1)
        else state
    loop2 state 0

let sum' player g f = fold' (fun s x -> s + f x) 0.0 player g

let p g u i t' j = 1.0 - 1.0 / u * sum' i g (fun k -> if k <> j then R g (t'-1) i j k else 0.0)

let S_eq g s s' =
    let rec loop i = if i < g.N then s i = s' i && loop (i+1) else true
    loop 0

let z g t s = 1.0 / float t * sum_time t (fun t -> if S_eq g (g.h t) s then 1.0 else 0.0)

