/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

/-!
# A Gibbs-style pointwise bound on the logarithm

## Main results

* `Real.mul_log_div_le_sub_of_nonneg`: `p * log (q / p) ≤ q - p` for `0 ≤ p` and `0 < q`.
-/

@[expose] public section

namespace Real

/-- **Gibbs-style pointwise bound**: `p * log (q / p) ≤ q - p` for `0 ≤ p`, `0 < q`. Underlying
real-analysis fact for the classical Klein/Gibbs inequality. -/
lemma mul_log_div_le_sub_of_nonneg {p q : ℝ} (hp_nn : 0 ≤ p) (hq_pos : 0 < q) :
    p * log (q / p) ≤ q - p := by
  obtain rfl | hp_pos := hp_nn.eq_or_lt
  · simpa using hq_pos.le
  · calc p * log (q / p)
        ≤ p * (q / p - 1) :=
          mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hq_pos hp_pos)) hp_pos.le
      _ = q - p := by field_simp

end Real
