// A Simple Adaptive Procedure Leading To Correlated Equilibrium

type Strategy = int
type Player = int

type Game = {
    N : Set<Player>
    S : Map<Player,Set<Strategy>>
    u : Map<Map<Player,Strategy>, float>
    }

let fold_strategies f state (g : Game) =
    Map.fold (fun next player strategies state ps ->
        Set.fold (fun state strategy -> next state (Map.add player strategy ps)) state strategies
        ) f g.S state Map.empty

let sum_strategies f g = fold_strategies (fun s ps -> s + f ps) 0.0 g

let Game_WF (g : Game) =
    Set.isEmpty g.N = false 
    && Set.forall (fun player -> Map.containsKey player g.S) g.N
    && fold_strategies (fun _ ps -> Map.containsKey ps g.u) true g
    && Map.forall (fun _ v -> (System.Double.IsNaN(v) || System.Double.IsInfinity(v)) = false) g.u

let cor_eq (e : float) (g : Game) psi =
    assert (Game_WF g)
    Set.fold (fun acc player ->
        let s = g.S.[player]
        Set.fold (fun acc i ->
            Set.fold (fun acc j ->
                sum_strategies (fun s ->
                    if ps.[player] = j then psi.[s] * (g.u)
                    else 0.0
                    )
                ) acc s
            ) acc s
        )
