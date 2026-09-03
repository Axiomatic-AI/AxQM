/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.NumberTheory.DiophantineApproximation.LegendreSharp
public import Mathlib.Data.ZMod.Units

/-!
# The generalized continued-fractions algorithm for the discrete logarithm

This file develops the classical post-processing step of the quantum discrete-logarithm algorithm
(*Nielsen & Chuang, Quantum Computation and Quantum Information*, §5.4.2, p. 239, Exercise 5.24).

## Main declarations

* `recoverNumerator` — read the numerator `k` of `k/r`, given `r`.
* `discreteLogRecover` — recover `s` in `ZMod r` from the two exact fractions by modular division.
* `discreteLog_of_estimates` — the end-to-end correctness of the algorithm: from the two estimates,
  continued fractions recovers both fractions and the modular combination returns `s`.
-/

open GenContFract

public section

namespace DiscreteLogRecovery

/-- Recover the integer numerator `k` of a fraction `q = k / r` from `q` and a known
denominator multiple `r`. Since `q * r = k`, the numerator is `(q * r).num`. -/
def recoverNumerator (q : ℚ) (r : ℕ) : ℤ := (q * r).num

/-- The generalized continued-fractions recovery of the discrete logarithm. Given two convergents
`q₁ ≈ (s·ℓ₂) / r` and `q₂ ≈ ℓ₂ / r` from continued fractions, and the known order `r`, return
`s` as an element of `ZMod r` by reading off the numerators and dividing modulo `r`. -/
def discreteLogRecover (q₁ q₂ : ℚ) (r : ℕ) : ZMod r :=
  (recoverNumerator q₁ r : ZMod r) * (recoverNumerator q₂ r : ZMod r)⁻¹

/-- End-to-end correctness of the generalized continued-fractions algorithm (steps 4–6 of N&C's
discrete-logarithm algorithm). Given estimates `φ₁ ≈ (s·ℓ₂) / r` and `φ₂ ≈ ℓ₂ / r` each accurate
to `1 / (2 r²)`, with `ℓ₂` coprime to `r` and `0 ≤ s < r`, continued fractions returns both exact
fractions and `discreteLogRecover` returns `s`. -/
theorem discreteLog_of_estimates {r : ℕ} (s ℓ : ℤ) (hs0 : 0 ≤ s) (hsr : s < r)
    (hcop : IsCoprime ℓ (r : ℤ)) {φ₁ φ₂ : ℝ}
    (h₁ : |φ₁ - ((s * ℓ) % r : ℤ) / (r : ℝ)| < 1 / (2 * (r : ℝ) ^ 2))
    (h₂ : |φ₂ - (ℓ % r : ℤ) / (r : ℝ)| < 1 / (2 * (r : ℝ) ^ 2)) :
    ∃ n₁ n₂ : ℕ,
      (GenContFract.of φ₁).convs n₁ = (((s * ℓ) % r : ℤ) / r : ℝ) ∧
      (GenContFract.of φ₂).convs n₂ = ((ℓ % r : ℤ) / r : ℝ) ∧
      ((discreteLogRecover (((s * ℓ) % r : ℤ) / r) ((ℓ % r : ℤ) / r) r).val : ℤ) = s := sorry

end DiscreteLogRecovery
