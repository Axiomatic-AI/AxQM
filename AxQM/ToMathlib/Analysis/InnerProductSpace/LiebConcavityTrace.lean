/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.CFCTensor
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import AxQM.ToMathlib.Analysis.InnerProductSpace.EuclideanConjVec
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Matricization

/-!
# Lieb's Theorem 1, trace form

The trace form `(A, B) ↦ re Tr(K† Aᵗ K B¹⁻ᵗ)`, for `t ∈ [0, 1]`, is jointly concave in the
positive semidefinite operators `A, B`.
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct

open Filter Topology

namespace TensorProduct

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

set_option synthInstance.maxHeartbeats 80000 in
-- `synthInstance` budget for the CFC `rpow` instance chain synthesizing `A ^ t` / `B ^ (1 - t)`
/-- **Lieb's Theorem (Nielsen & Chuang, Theorem 11.11), trace form, for positive matrices.** For a
matrix `K : EuclideanSpace ℂ ι →L E` and exponent `t ∈ [0, 1]`, the function
`f(A, B) = re Tr(K† Aᵗ K B¹⁻ᵗ)` is jointly concave in the **positive semidefinite** operators
`A, B`, in the shape of N&C's definition of joint concavity (11.96). -/
theorem concaveAt_trace_one_sub_isPositive (K : EuclideanSpace ℂ ι →L[ℂ] E) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {A₁ A₂ : E →L[ℂ] E} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {B₁ B₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          (ContinuousLinearMap.adjoint K ∘L (A₁ ^ t) ∘L K ∘L (B₁ ^ (1 - t)))) +
        b • RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          (ContinuousLinearMap.adjoint K ∘L (A₂ ^ t) ∘L K ∘L (B₂ ^ (1 - t)))) ≤
      RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (ContinuousLinearMap.adjoint K ∘L ((a • A₁ + b • A₂) ^ t) ∘L K ∘L
          ((a • B₁ + b • B₂) ^ (1 - t)))) := sorry

set_option synthInstance.maxHeartbeats 80000 in
-- `synthInstance` budget for the CFC `rpow` instance chain synthesizing `X.1 ^ t` / `X.2 ^ (1 - t)`
/-- **Lieb's Theorem (N&C Theorem 11.11), positive matrices, packaged as `ConcaveOn`.** The trace
form `f(A, B) = re Tr(K† Aᵗ K B¹⁻ᵗ)` (`t ∈ [0, 1]`) is jointly concave on the product of the two
**positive semidefinite** cones. -/
theorem concaveOn_trace_one_sub_isPositive (K : EuclideanSpace ℂ ι →L[ℂ] E) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ConcaveOn ℝ ({A : E →L[ℂ] E | 0 ≤ A} ×ˢ
        {B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι | 0 ≤ B})
      (fun X => RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (ContinuousLinearMap.adjoint K ∘L (X.1 ^ t) ∘L K ∘L (X.2 ^ (1 - t))))) := sorry

end TensorProduct
