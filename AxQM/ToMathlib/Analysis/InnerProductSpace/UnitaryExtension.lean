/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Unitary extension of an inner-product-preserving map on a subspace

Let `V` be a finite-dimensional inner product space over an `RCLike` field `𝕜` and let `W` be a
subspace of `V`. If a linear map `U : W → V` *preserves inner products*, that is
`⟪U w₁, U w₂⟫ = ⟪w₁, w₂⟫` for all `w₁, w₂ ∈ W`, then `U` extends to a **unitary** operator on all
of `V` — a linear isometry equivalence `V ≃ₗᵢ[𝕜] V` agreeing with `U` on `W`.

## Main results

* `LinearMap.unitaryExtend`: the unitary extension `V ≃ₗᵢ[𝕜] V` of an inner-product-preserving
  `U : W →ₗ[𝕜] V`.
* `LinearMap.unitaryExtend_apply`: the extension agrees with `U` on `W`.
* `LinearMap.exists_unitaryExtend`: the existence statement of Exercise 2.67 — there is a unitary
  `U' : V ≃ₗᵢ[𝕜] V` with `U' w = U w` for every `w ∈ W`.
-/

open scoped InnerProductSpace

@[expose] public section

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] {W : Submodule 𝕜 V}

namespace LinearMap

/-- The **unitary extension** of an inner-product-preserving linear map `U : W → V` on a subspace
`W` of a finite-dimensional inner product space `V`. -/
noncomputable def unitaryExtend (U : W →ₗ[𝕜] V)
    (hU : ∀ w₁ w₂ : W, ⟪U w₁, U w₂⟫_𝕜 = ⟪w₁, w₂⟫_𝕜) : V ≃ₗᵢ[𝕜] V :=
  ((U.isometryOfInner hU).extend).toLinearIsometryEquiv rfl

/-- The unitary extension `U.unitaryExtend` agrees with `U` on the subspace `W`. -/
@[simp]
theorem unitaryExtend_apply (U : W →ₗ[𝕜] V)
    (hU : ∀ w₁ w₂ : W, ⟪U w₁, U w₂⟫_𝕜 = ⟪w₁, w₂⟫_𝕜) (w : W) :
    U.unitaryExtend hU w = U w := by
  simp only [unitaryExtend, LinearIsometry.coe_toLinearIsometryEquiv,
    LinearIsometry.extend_apply, LinearMap.coe_isometryOfInner]

/-- **Nielsen & Chuang, Exercise 2.67.** A linear map `U : W → V` on a subspace `W` of a
finite-dimensional inner product space `V` that preserves inner products extends to a unitary
operator on all of `V`. -/
theorem exists_unitaryExtend (U : W →ₗ[𝕜] V)
    (hU : ∀ w₁ w₂ : W, ⟪U w₁, U w₂⟫_𝕜 = ⟪w₁, w₂⟫_𝕜) :
    ∃ U' : V ≃ₗᵢ[𝕜] V, ∀ w : W, U' w = U w := sorry

end LinearMap
