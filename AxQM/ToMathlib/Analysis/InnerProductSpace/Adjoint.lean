/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Adjoints of rank-one maps, and conjugation by a linear isometry equivalence

## Main results

* `ContinuousLinearMap.adjoint_toLinearMap`: the LM-coercion of a CLM-adjoint is the
  LM-adjoint of the LM-coercion.
* `LinearIsometryEquiv.conjStarAlgEquiv_toLinearMap` and `…_isSelfAdjoint_iff`: conjugation
  by an isometry equivalence, and its interaction with self-adjointness.

-/

@[expose] public section

noncomputable section
open Module RCLike
open scoped ComplexConjugate
variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
open InnerProductSpace
namespace ContinuousLinearMap
variable {T : E →L[𝕜] E} [CompleteSpace E]
open ContinuousLinearMap

/-- A rank-one self-projector is its own measurement effect: for a unit vector `x`,
`(rankOne x x)† ∘ (rankOne x x) = rankOne x x`. -/
theorem _root_.InnerProductSpace.adjoint_rankOne_comp_self {x : E} (hx : ‖x‖ = 1) :
    adjoint (rankOne 𝕜 x x) ∘L rankOne 𝕜 x x = rankOne 𝕜 x x := by
  rw [adjoint_rankOne]
  exact (isStarProjection_rankOne_self hx).isIdempotentElem

end ContinuousLinearMap
end

noncomputable section
open Module RCLike
open scoped ComplexConjugate
variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
open InnerProductSpace
namespace LinearMap
variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]

/-- For a continuous linear map `T`, the LM-coercion of its CLM-adjoint equals the LM-adjoint
of its LM-coercion. -/
theorem _root_.ContinuousLinearMap.adjoint_toLinearMap [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) :
    (T.adjoint : F →L[𝕜] E).toLinearMap = LinearMap.adjoint T.toLinearMap :=
  rfl

end LinearMap
end

noncomputable section
open Module RCLike
open scoped ComplexConjugate
variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
open InnerProductSpace
namespace LinearMap
variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]

/-- For a symmetric operator on a finite-dimensional inner product space, the orthogonal
complement of the kernel equals the range. -/
theorem IsSymmetric.range_eq_orthogonal_ker {T : E →ₗ[𝕜] E} (hT : LinearMap.IsSymmetric T) :
    LinearMap.range T = (LinearMap.ker T)ᗮ := by
  rw [LinearMap.orthogonal_ker, hT.adjoint_eq]

end LinearMap
end

noncomputable section
open Module RCLike
open scoped ComplexConjugate
variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
open InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
namespace LinearIsometryEquiv

/-- The LinearMap coercion of `e.conjStarAlgEquiv T` is the `LinearEquiv.conj` form of
the LinearMap coercion of `T`. Definitional bridge from the CLM-level StarAlgEquiv to the
LM-level conjugation. -/
@[simp]
theorem conjStarAlgEquiv_toLinearMap (e : H ≃ₗᵢ[𝕜] K) (T : H →L[𝕜] H) :
    ((e.conjStarAlgEquiv T : K →L[𝕜] K) : K →ₗ[𝕜] K) =
      e.toLinearEquiv.conj (T : H →ₗ[𝕜] H) := rfl

end LinearIsometryEquiv
end

noncomputable section
open Module RCLike
open scoped ComplexConjugate
variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
open InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
namespace LinearIsometryEquiv

/-- An operator on `H` is self-adjoint iff its image under conjugation by a linear isometry
equivalence is self-adjoint on `K`. -/
@[simp]
theorem conjStarAlgEquiv_isSelfAdjoint_iff (e : H ≃ₗᵢ[𝕜] K) {T : H →L[𝕜] H} :
    IsSelfAdjoint (e.conjStarAlgEquiv T) ↔ IsSelfAdjoint T := by
  simp only [_root_.IsSelfAdjoint, ← map_star e.conjStarAlgEquiv,
    EmbeddingLike.apply_eq_iff_eq]

end LinearIsometryEquiv
end
