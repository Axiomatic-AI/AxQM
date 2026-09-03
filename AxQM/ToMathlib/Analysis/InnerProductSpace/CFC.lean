/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.Trace
public import AxQM.ToMathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Closed-form continuous functional calculus on a finite-dimensional inner product space
-/

@[expose] public section

open InnerProductSpace ContinuousFunctionalCalculus Module.End

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open scoped ComplexOrder in
/-- **Uniqueness of the positive square root**: for a positive operator `x`, the CFC sqrt of `x * x`
recovers `x`. Equivalently, two positive operators with equal squares are equal — applying this
lemma to both sides of `A * A = B * B` (`0 ≤ A`, `0 ≤ B`) gives `A = cfc Real.sqrt (A * A) = cfc
Real.sqrt (B * B) = B`. -/
theorem cfc_real_sqrt_mul_self_eq_self_of_nonneg
    {x : E →L[ℂ] E} (hx : 0 ≤ x) :
    cfc Real.sqrt (x * x) = x := by
  conv_rhs => rw [← cfc_id ℝ x]
  rw [← sq, ← cfc_comp_pow (R := ℝ) Real.sqrt 2 x]
  exact cfc_congr fun y hy ↦ Real.sqrt_sq (spectrum_nonneg_of_nonneg hx hy)

end ContinuousLinearMap
