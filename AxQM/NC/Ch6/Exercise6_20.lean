/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BitOracleZeroError

/-!
# Nielsen & Chuang, Exercise 6.20 (`Q₀(OR) ≥ N` by the method of polynomials)

*(N&C p. 274.)*

Show Q0(OR) >= N by building a polynomial representing OR from a zero-error quantum circuit.

* `orZeroError_bornProb_query_lower_bound`
-/

open scoped InnerProductSpace

namespace AxQM

variable {S : QSystem} {σ ω : Type*}

/-- **Nielsen & Chuang, Exercise 6.20: `Q₀(OR) ≥ N`.** Consider a `T`-query quantum algorithm on a
register `S` with a computational basis `|i,b,j⟩` indexed by `σ × Bool × ω`
(`prob : QuantumQueryProblem S σ ω`), unitary schedule `U`, input pure state `ψ`, and query state
`ψ(X)_T = prob.queryState U ψ X T` against the bit-oracle for `X : σ → Bool`. Measure the output in
the computational basis (`prob.measurement`) and let `answer0` be the outcomes decoded as
"output `0`". If the circuit **computes OR with zero error**, i.e.

* it never outputs `0` when `OR(X) = 1` — the answer-`0` probability
  `∑_{k ∈ answer0} p(k | ψ(X)_T)` is `0` for every `X` with some `Xᵢ = true` (`hnever`),

each `p(k | ψ(X)_T)` being the genuine Born probability
`prob.measurement.bornProb (prob.queryState U ψ X T).toState k`, then
`Fintype.card σ ≤ T`. Since this bounds the query count `T` of *every* zero-error `T`-query OR
circuit from below by `N = Fintype.card σ`, the zero-error quantum query complexity satisfies
`Q₀(OR) ≥ N`.
-/
theorem orZeroError_bornProb_query_lower_bound [Fintype σ] [Fintype ω]
    (prob : QuantumQueryProblem S σ ω) (U : ℕ → Evolution S) (ψ : PureState S) (T : ℕ)
    (answer0 : Finset (σ × Bool × ω))
    (hnever : ∀ X : σ → Bool, (∃ i, X i = true) →
      (∑ k ∈ answer0, prob.measurement.bornProb (prob.queryState U ψ X T).toState k) = 0)
    (hcorrect : 1 / 2 < ∑ k ∈ answer0,
      prob.measurement.bornProb (prob.queryState U ψ (fun _ => false) T).toState k) :
    Fintype.card σ ≤ T := sorry

end AxQM
