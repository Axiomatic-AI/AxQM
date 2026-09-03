/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions

/-!
# Legendre's Theorem on rational approximation: sharpness of the strict hypothesis

*Nielsen & Chuang, Quantum Computation and Quantum Information*, **Theorem 5.1** — used in the
continued-fractions step of order finding, §5.3.1.

## Main statements

* `Real.not_forall_exists_convs_eq_of_abs_sub_le` — **the `≤`-version of Theorem 5.1 is false**: it
  is *not* the case that `|ξ - q| ≤ 1 / (2 * q.den ^ 2)` forces `q` to be a convergent of `ξ`.
-/

open GenContFract

public section

namespace Real

/-- **Sharpness of Legendre's Theorem.** The strict inequality cannot be relaxed to `≤`: it is
*not* true that every rational `q` with `|ξ - q| ≤ 1 / (2 * q.den ^ 2)` is a convergent of `ξ`.

This is *Nielsen & Chuang* Theorem 5.1 read literally, with its non-strict hypothesis `≤`; the
faithful, correct statement is the strict form. -/
theorem not_forall_exists_convs_eq_of_abs_sub_le :
    ¬ ∀ (ξ : ℝ) (q : ℚ), |ξ - (q : ℝ)| ≤ 1 / (2 * (q.den : ℝ) ^ 2) →
      ∃ n, (GenContFract.of ξ).convs n = (q : ℝ) := sorry

end Real
