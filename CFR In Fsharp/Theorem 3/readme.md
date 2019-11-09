Surprisingly, theorem 3 from the `Regret Minimization in Games with Incomplete Information` is outright wrong. There is a counterexample in both F# and Python.

In the tests there are a bunch of simplifying assumptions:
* T=1. Policies are not summed across time.
* Chance nodes are ommited.
* I am assuming that the theorem is intended to work for all non-empty sets, so maximizing over a singleton set is the same as extracting from it directly. Hence I am using only two policies in the comparison.
* I am considering only games with one player. These are equivalent to two player games where the other player has only one action. As a result, CFR reach probabilities are 1 everywhere and so are ommited where they'd multiply the utilities.
