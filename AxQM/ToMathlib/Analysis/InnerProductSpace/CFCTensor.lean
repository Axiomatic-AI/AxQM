/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.CFC
public import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorPower
public import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt

/-!
# Tensor products of self-adjoint and positive operators

How self-adjointness and positivity of continuous linear maps on a finite-dimensional complex
Hilbert space transfer along `TensorProduct.mapL`.

## Main results

- `IsSelfAdjoint.tensorMapL`: the tensor product of self-adjoint continuous linear maps is
  self-adjoint.
- `TensorProduct.mapL_isPositive`: the tensor product of positive operators is positive.
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct

/-- The tensor product of self-adjoint continuous linear maps is self-adjoint. -/
theorem IsSelfAdjoint.tensorMapL {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]
    {A : E →L[ℂ] E} {B : F →L[ℂ] F} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (TensorProduct.mapL A B) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (LinearMap.IsSymmetric.tensorMap hA.isSymmetric hB.isSymmetric)

namespace TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

variable [CompleteSpace E] [CompleteSpace F]

/-- The tensor product of nonneg operators is nonneg. -/
theorem mapL_nonneg {A : E →L[ℂ] E} {B : F →L[ℂ] F} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ mapL A B := by
  rw [← CFC.sqrt_mul_sqrt_self A hA, ← CFC.sqrt_mul_sqrt_self B hB, mapL_mul]
  exact ((CFC.sqrt_nonneg A).isSelfAdjoint.tensorMapL
    (CFC.sqrt_nonneg B).isSelfAdjoint).mul_self_nonneg

/-- **N&C Exercise 2.31**: the tensor product of two *positive operators* is positive. `mapL A B` is
a positive operator (`ContinuousLinearMap.IsPositive`, i.e. symmetric with `0 ≤ re ⟪·, ·⟫` —
N&C's defining property of a positive operator) whenever both `A` and `B` are. -/
theorem mapL_isPositive {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : A.IsPositive) (hB : B.IsPositive) :
    (mapL A B).IsPositive := sorry

end TensorProduct
