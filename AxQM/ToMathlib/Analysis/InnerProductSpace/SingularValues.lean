/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The singular value decomposition of a linear map

## Main results

* `LinearMap.svdRight`, `LinearMap.svdLeft`, `LinearMap.svd_apply`: the singular vectors and
  the decomposition.
* `ContinuousLinearMap.adjoint_comp_self_apply_svdRight`: the right singular vectors are
  eigenvectors of `T† ∘ T`.

-/

@[expose] public section

section
open Module InnerProductSpace
namespace LinearMap
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/-- The right singular vectors of `T`: an orthonormal eigenbasis of `T† ∘ T`. -/
@[expose]
noncomputable def svdRight : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

end LinearMap
end

section
open Module InnerProductSpace
namespace LinearMap
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

@[simp] theorem svdRight_apply (i : Fin (finrank 𝕜 E)) :
    T.svdRight i = T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i := rfl

end LinearMap
end

section
open Module InnerProductSpace
namespace LinearMap
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/-- The left singular vectors of `T`: `σᵢ⁻¹ • T uᵢ` (junk when `σᵢ = 0`). -/
@[expose]
noncomputable def svdLeft (i : Fin (finrank 𝕜 E)) : F :=
  ((T.singularValues i.val : 𝕜))⁻¹ • T (T.svdRight i)

end LinearMap
end

section
open Module InnerProductSpace
namespace LinearMap
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

@[simp] theorem svdLeft_apply (i : Fin (finrank 𝕜 E)) :
    T.svdLeft i = ((T.singularValues i.val : 𝕜))⁻¹ • T (T.svdRight i) := rfl

end LinearMap
end

section
open Module InnerProductSpace
namespace LinearMap
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/-- A right singular vector with zero singular value is in the kernel of `T`. -/
theorem apply_svdRight_eq_zero_of_singularValues_eq_zero (i : Fin (finrank 𝕜 E))
    (hi : T.singularValues i.val = 0) : T (T.svdRight i) = 0 := by
  have hsq : T.singularValues i.val ^ 2 = 0 := by simp [hi]
  rw [T.sq_singularValues_fin rfl] at hsq
  rw [← norm_eq_zero (E := F), ← sq_eq_zero_iff, ← inner_self_eq_norm_sq (𝕜 := 𝕜),
    ← T.adjoint_inner_right, svdRight_apply, ← LinearMap.comp_apply,
    T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i, inner_smul_right,
    hsq, RCLike.ofReal_zero, zero_mul, map_zero]

end LinearMap
end

section
open Module InnerProductSpace
namespace LinearMap
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/-- A left singular vector with zero singular value is itself zero. -/
theorem svdLeft_eq_zero_of_singularValues_eq_zero (i : Fin (finrank 𝕜 E))
    (hi : T.singularValues i.val = 0) : T.svdLeft i = 0 := by
  rw [svdLeft_apply, T.apply_svdRight_eq_zero_of_singularValues_eq_zero i hi, smul_zero]

end LinearMap
end

section
open Module InnerProductSpace
namespace LinearMap
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/-- The fundamental SVD relation: applying `T` to a right singular vector scales the
corresponding left singular vector by the singular value. Holds even for the junk
left vectors when `σᵢ = 0`, since both sides vanish. -/
theorem apply_svdRight (i : Fin (finrank 𝕜 E)) :
    T (T.svdRight i) = (T.singularValues i.val : 𝕜) • T.svdLeft i := by
  rw [svdLeft_apply, smul_smul]
  by_cases hi : T.singularValues i.val = 0
  · rw [T.apply_svdRight_eq_zero_of_singularValues_eq_zero i hi, smul_zero]
  · rw [mul_inv_cancel₀ (by exact_mod_cast hi), one_smul]

end LinearMap
end

section
open Module InnerProductSpace
namespace LinearMap
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/-- **Singular value decomposition (vector form)**: any linear map `T : E →ₗ[𝕜] F`
between finite-dimensional inner product spaces admits a factorization
`T x = ∑ σᵢ • ⟨uᵢ, x⟩ • vᵢ` where the `uᵢ` are an orthonormal eigenbasis of
`T† ∘ T` (the right singular vectors) and the `vᵢ = σᵢ⁻¹ • T uᵢ` are orthonormal
on the support `{i | σᵢ ≠ 0}` (the left singular vectors). -/
theorem svd_apply (x : E) : T x =
    ∑ i, (T.singularValues i.val : 𝕜) • ⟪T.svdRight i, x⟫_𝕜 • T.svdLeft i := by
  conv_lhs => rw [← T.svdRight.sum_repr' x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, T.apply_svdRight i, smul_smul, smul_smul, mul_comm]

end LinearMap
end

section
open Module InnerProductSpace
namespace ContinuousLinearMap
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →L[𝕜] F)

/-- CLM-level apply-form for `T.adjoint ∘L T` on the right singular vectors:
`(T.adjoint ∘L T) (svdRight i) = σᵢ² • svdRight i`. The right singular vectors are eigenvectors
of `T.adjoint ∘L T` with eigenvalue `σᵢ²`. -/
@[simp]
theorem adjoint_comp_self_apply_svdRight [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F)
    (i : Fin (finrank 𝕜 E)) :
    (T.adjoint ∘L T) (T.toLinearMap.svdRight i) =
      ((T.toLinearMap.singularValues i.val) ^ 2 : 𝕜) • T.toLinearMap.svdRight i := by
  have hsym := T.toLinearMap.isSymmetric_adjoint_comp_self
  rw [← ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp, T.adjoint_toLinearMap,
    LinearMap.svdRight_apply, hsym.apply_eigenvectorBasis rfl,
    ← T.toLinearMap.sq_singularValues_fin rfl]
  push_cast
  rfl

end ContinuousLinearMap
end
