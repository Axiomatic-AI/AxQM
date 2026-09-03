/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Topology.Algebra.Module.LinearMap

/-!
# Membership in the kernel of a continuous linear map

## Main results

* `ContinuousLinearMap.mem_ker`: `x ∈ ker f ↔ f x = 0`.

-/

@[expose] public section

section
open LinearMap (ker range)
open Topology Filter Pointwise
universe u v w u'
namespace ContinuousLinearMap
variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} {M₁ : Type*} [TopologicalSpace M₁]
  [AddCommMonoid M₁] {M'₁ : Type*} [TopologicalSpace M'₁] [AddCommMonoid M'₁] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁] [Module R₁ M'₁]
  [Module R₂ M₂] [Module R₃ M₃]

@[simp]
theorem mem_ker {f : M₁ →SL[σ₁₂] M₂} {x : M₁} : x ∈ LinearMap.ker (f : M₁ →ₛₗ[σ₁₂] M₂) ↔ f x = 0 :=
  LinearMap.mem_ker

end ContinuousLinearMap
end
