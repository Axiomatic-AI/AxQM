/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SearchOptimality

/-!
# Nielsen & Chuang, Exercise 6.16 (average-case optimality of quantum search)

*(N&C p. 270.)*

Show O(sqrt N) oracle calls still needed when error is averaged uniformly over x (<1/2).

* `search_bornProb_averaged_success_imp_queries_ge` — the clean `Ω(√N)` conclusion `√N/8 ≤ k` (for
  `N ≥ 21`).
-/

open scoped InnerProductSpace

namespace AxQM

variable {S : QSystem} {N : ℕ}

/-- **Nielsen & Chuang, Exercise 6.16 — `O(√N)` oracle calls are still required.** Under the
uniformly averaged success criterion `N/2 ≤ ∑ₓ p(x | ψˣ_k)` (Born probabilities of returning the
marked item), a `k`-query quantum search algorithm needs `k ≥ √N/8` for `N ≥ 21`: `Ω(√N)` oracle
calls remain necessary even when the error is averaged uniformly over `x`, rather than bounded for
every `x`.

The average-case hypothesis is genuinely weaker than N&C's worst-case `|⟨x|ψˣ_k⟩|² ≥ 1/2` for all
`x` (it is implied by it), so this strengthens the §6.6 optimality theorem exactly as the exercise
asks. -/
theorem search_bornProb_averaged_success_imp_queries_ge (prob : QuantumSearchProblem S N)
    (U : ℕ → Evolution S) (ψ : PureState S) (k : ℕ) (hN : 21 ≤ N)
    (havg : (N : ℝ) / 2 ≤ ∑ x, prob.measurement.bornProb (prob.queryState U ψ k x).toState x) :
    Real.sqrt N / 8 ≤ (k : ℝ) := sorry

end AxQM
