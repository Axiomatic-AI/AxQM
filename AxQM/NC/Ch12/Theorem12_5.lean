/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.TypicalSubspace

/-!
# N&C Theorem 12.5 — the typical subspace theorem (parts (1) and (2))

*(N&C p. 543.)*

Typical subspace theorem: tr(P rho^n) bounds, dim bounds, small-subspace bound.

* `State.typicalSubspace_bornProb_ge` — Part (1) (N&C Eq. 12.43).
* `State.typicalSubspaceDim_bounds` — Part (2) (N&C Eq. 12.44).
* `State.smallSubspace_bornProb_le` — Part (3) (N&C Eq. 12.45).
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Typical subspace theorem, part (1)** (Nielsen & Chuang, Theorem 12.5, Eq. 12.43): the source
`ρ^⊗n` lands in the ε-typical subspace with probability `≥ 1 − δ` for all sufficiently large
`n`. Fix `ε > 0`; then for any `δ > 0` there is an `N` such that for every `n ≥ N` the Born
probability of the typical outcome of the projective measurement `{P(n, ε), I − P(n, ε)}` on
`ρ^⊗n` is at least `1 − δ` — i.e. `tr(P(n, ε) ρ^⊗n) ≥ 1 − δ`.
-/
theorem State.typicalSubspace_bornProb_ge (ρ : State S) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      1 - δ ≤ (ρ.typicalSubspaceMeasurement n ε).bornProb (ρ.tensorPow n) true := sorry

/-- **Typical subspace theorem, part (2)** (Nielsen & Chuang, Theorem 12.5, Eq. 12.44): the
dimension of the ε-typical subspace is `2^{n S(ρ)}` up to the exponential tolerance `ε`. Fix `ε
> 0` and `δ > 0`; then for all sufficiently large `n` the dimension `|T(n, ε)| = tr(P(n, ε))`
satisfies

`(1 − δ) exp(n (S(ρ) − ε)) ≤ |T(n, ε)| ≤ exp(n (S(ρ) + ε))`

(in nats; N&C's base-`2` `(1 − δ) 2^{n(S(ρ)−ε)} ≤ |T(n, ε)| ≤ 2^{n(S(ρ)+ε)}`).
-/
theorem State.typicalSubspaceDim_bounds (ρ : State S) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      (1 - δ) * Real.exp (n * (ρ.vonNeumannEntropy - ε)) ≤ (ρ.typicalSubspaceDim n ε : ℝ) ∧
        (ρ.typicalSubspaceDim n ε : ℝ) ≤ Real.exp (n * (ρ.vonNeumannEntropy + ε)) := sorry

/-- **Typical subspace theorem, part (3)** (Nielsen & Chuang, Theorem 12.5, Eq. 12.45): a *small*
subspace carries negligible weight of the source.
-/
theorem State.smallSubspace_bornProb_le (ρ : State S) {R : ℝ} (hR : R < ρ.vonNeumannEntropy)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ M : Measurement Bool (S ^⊗ₛ n), M.IsProjective →
      (M.trueSubspaceDim : ℝ) ≤ Real.exp (n * R) →
        M.bornProb (ρ.tensorPow n) true ≤ δ := sorry

end AxQM
