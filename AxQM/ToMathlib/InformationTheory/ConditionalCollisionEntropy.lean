/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.CollisionEntropy
public import AxQM.ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# Conditional collision entropy and the privacy-amplification tail bound

For a finite joint distribution `p : ι × κ → ℝ` of a pair of random variables `(X, U)` (a
probability mass function when `p ≥ 0` and `∑ p = 1`), this file develops the **conditional
collision entropy** `Hc(X | U = u)` — the collision entropy (Rényi entropy of order 2) of the
conditional distribution of `X` given the *specific* value `U = u` — and proves the tail bound
underlying privacy amplification and information reconciliation.

## Main definitions

- `Real.condDistribGivenSnd p u`: the conditional distribution `x ↦ p(x, u) / p_U(u)` of `X`
  given `U = u`.
- `Real.condCollisionEntropy p u`: `Hc(X | U = u) = -log₂ (∑ₓ p(x | u)²)`.

## Main results

- `Real.prob_condCollisionEntropy_ge` — **Nielsen & Chuang, Theorem 12.17**: for a security
  parameter `s > 0`, with probability at least `1 - 2⁻ˢ` (measured by `p_U`) the value `U = u`
  satisfies `Hc(X | U = u) ≥ Hc(X) - 2·log₂|U| - 2s`.
-/

@[expose] public section

namespace Real

variable {ι κ : Type*} [Fintype ι]

/-- The **conditional distribution** of `X` given `U = u`: `x ↦ p(x, u) / p_U(u)`, where
`p_U(u) = Real.marginalSnd p u`. When `p_U(u) = 0` this is the zero function. -/
noncomputable def condDistribGivenSnd (p : ι × κ → ℝ) (u : κ) : ι → ℝ :=
  fun x ↦ p (x, u) / marginalSnd p u

/-- The **conditional collision entropy** `Hc(X | U = u) = -log₂ (∑ₓ p(x | u)²)`, the collision
entropy of the conditional distribution of `X` given `U = u`. -/
noncomputable def condCollisionEntropy (p : ι × κ → ℝ) (u : κ) : ℝ :=
  collisionEntropy (condDistribGivenSnd p u)

variable [Fintype κ]

/-- **Nielsen & Chuang, Theorem 12.17** (privacy amplification / information reconciliation). Let
`X` and `U` be jointly distributed random variables with joint law `p : ι × κ → ℝ` (`p ≥ 0`, `∑
p = 1`), and let `s > 0` be a security parameter. Then, with probability at least `1 - 2⁻ˢ`
(measured by the marginal `p_U`), the value `U = u` satisfies `Hc(X | U = u) ≥ Hc(X) - 2·log₂|U|
- 2s`, where `Hc(X) = Real.collisionEntropy (marginalFst p)` and `|U| = Fintype.card κ`.

The event is recorded as a lower bound `1 - 2⁻ˢ ≤ ∑ᵤ p_U(u)` over the `u` at which the
inequality holds.

Nielsen & Chuang state this for a security parameter `s > 0`; the statement here is for every
real `s`.
-/
theorem prob_condCollisionEntropy_ge (p : ι × κ → ℝ) (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1)
    (s : ℝ) :
    1 - (2 : ℝ) ^ (-s) ≤ ∑ u ∈ Finset.univ.filter
        (fun u ↦ collisionEntropy (marginalFst p) - 2 * Real.logb 2 (Fintype.card κ) - 2 * s
          ≤ condCollisionEntropy p u),
      marginalSnd p u := sorry

end Real
