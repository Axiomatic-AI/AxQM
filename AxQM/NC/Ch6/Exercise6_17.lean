/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SearchLowerBoundMultiSolution

/-!
# Nielsen & Chuang, Exercise 6.17 (optimality of search with multiple solutions)

*(N&C p. 271.)*

Show O(sqrt(N/M)) oracle applications required to find a solution when there are M solutions.

* `search_bornProb_multi_solution_imp_queries_ge`
-/

open scoped InnerProductSpace
open Finset

namespace AxQM

variable {S : QSystem} {N : ℕ}

/-- **Nielsen & Chuang, Exercise 6.17 — `Ω(√(N/M))` oracle applications are required.** For a
`k`-query quantum search algorithm on a register `S` with a marked computational basis
(`prob : QuantumSearchProblem S N`), initial pure state `ψ` and arbitrary unitary schedule `U`, if
for **every** size-`M` marked world `s` the algorithm *finds a solution* with probability at least
one half —
`1/2 ≤ ∑_{y∈s} p(y | ψˢ_k)` with each `p(y | ψˢ_k)` the genuine Born probability
`prob.measurement.bornProb (prob.setQueryState U ψ s k).toState y` of reading the marked item `y`
back — then
`k ≥ ½·(√(N/(2M)) − 1)`.

This is the multiple-solution optimality bound of N&C §6.6: `M` solutions still need `Ω(√(N/M))`
queries. -/
theorem search_bornProb_multi_solution_imp_queries_ge (prob : QuantumSearchProblem S N)
    (U : ℕ → Evolution S) (ψ : PureState S) {M : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) (k : ℕ)
    (hsucc : ∀ s ∈ (univ : Finset (Fin N)).powersetCard M,
        (1 : ℝ) / 2 ≤ ∑ y ∈ s, prob.measurement.bornProb (prob.setQueryState U ψ s k).toState y) :
    (1 / 2 : ℝ) * (Real.sqrt ((N : ℝ) / (2 * M)) - 1) ≤ (k : ℝ) := sorry

end AxQM
