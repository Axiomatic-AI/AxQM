/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.CFC
public import AxQM.ToMathlib.Topology.Algebra.Module.LinearMap
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Positive
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Adjoint
public import AxQM.ToMathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!

# Polar decomposition of a finite-dimensional operator

For `T : E →L[𝕜] F` a continuous linear map between finite-dimensional inner product spaces
(possibly with `E ≠ F`), this file constructs the **polar decomposition** `T = U |T|`.

## Main results

* `ContinuousLinearMap.polar_decomposition`: `T = T.polarPart ∘L T.absoluteValue`.
* `ContinuousLinearMap.absoluteValue_isPositive`: `T.absoluteValue.IsPositive`.
* `ContinuousLinearMap.absoluteValue_sq`: `T.absoluteValue ∘L T.absoluteValue = T† ∘L T`,
  the canonical characterization of `|T|`.
* `ContinuousLinearMap.polar_decomposition_unique`: if `T = U' ∘L P'` with `P'` positive,
  `U'` a partial isometry, and `kernel U' = kernel P'`, then `P' = absoluteValue T` and
  `U' = polarPart T`.
-/

@[expose] public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

open Module InnerProductSpace
open scoped InnerProduct

namespace ContinuousLinearMap

variable (T : E →L[𝕜] F)

/-- The **absolute value** `|T|` of an operator `T`, constructed from the singular
value decomposition as `∑ σᵢ • rankOne uᵢ uᵢ` where `uᵢ` are the right singular
vectors. Lives on the source space `E` since `|T| = sqrt(T† ∘ T)`. -/
noncomputable def absoluteValue : E →L[𝕜] E :=
  ∑ i : Fin (finrank 𝕜 E), (T.toLinearMap.singularValues i.val : 𝕜) •
    rankOne 𝕜 (T.toLinearMap.svdRight i) (T.toLinearMap.svdRight i)

/-- The **polar part** `U` of an operator `T : E →L[𝕜] F`, constructed from the singular value
decomposition as `∑ rankOne vᵢ uᵢ` sending each right singular vector `uᵢ ∈ E` to the
corresponding left singular vector `vᵢ ∈ F`. -/
noncomputable def polarPart : E →L[𝕜] F :=
  ∑ i : Fin (finrank 𝕜 E),
    rankOne 𝕜 (T.toLinearMap.svdLeft i) (T.toLinearMap.svdRight i)

@[simp] theorem absoluteValue_eq_sum : T.absoluteValue =
    ∑ i : Fin (finrank 𝕜 E), (T.toLinearMap.singularValues i.val : 𝕜) •
      rankOne 𝕜 (T.toLinearMap.svdRight i) (T.toLinearMap.svdRight i) := rfl

@[simp] theorem polarPart_eq_sum : T.polarPart =
    ∑ i : Fin (finrank 𝕜 E),
      rankOne 𝕜 (T.toLinearMap.svdLeft i) (T.toLinearMap.svdRight i) := rfl

/-- `|T|` diagonalizes the right singular vectors with eigenvalue `σᵢ`. -/
@[simp] theorem absoluteValue_apply_svdRight (i : Fin (finrank 𝕜 E)) :
    T.absoluteValue (T.toLinearMap.svdRight i) =
      (T.toLinearMap.singularValues i.val : 𝕜) • T.toLinearMap.svdRight i := by
  classical
  simp only [absoluteValue_eq_sum, sum_apply, ContinuousLinearMap.smul_apply, rankOne_apply]
  rw [Finset.sum_eq_single i (fun j _ hji ↦ ?_) (by simp)]
  · rw [orthonormal_iff_ite.mp T.toLinearMap.svdRight.orthonormal i i, if_pos rfl,
      smul_smul, mul_one]
  · rw [orthonormal_iff_ite.mp T.toLinearMap.svdRight.orthonormal j i, if_neg hji,
      zero_smul, smul_zero]

/-- The polar part `U` sends each right singular vector to the corresponding left
singular vector. -/
@[simp] theorem polarPart_apply_svdRight (i : Fin (finrank 𝕜 E)) :
    T.polarPart (T.toLinearMap.svdRight i) = T.toLinearMap.svdLeft i := by
  classical
  simp only [polarPart_eq_sum, sum_apply, rankOne_apply]
  rw [Finset.sum_eq_single i (fun j _ hji ↦ ?_) (by simp)]
  · rw [orthonormal_iff_ite.mp T.toLinearMap.svdRight.orthonormal i i, if_pos rfl, one_smul]
  · rw [orthonormal_iff_ite.mp T.toLinearMap.svdRight.orthonormal j i, if_neg hji, zero_smul]

/-- The polar decomposition: `T = polarPart T ∘L absoluteValue T`. -/
theorem polar_decomposition : T = T.polarPart ∘L T.absoluteValue := by
  ext x
  have hx : x = ∑ i, ⟪T.toLinearMap.svdRight i, x⟫_𝕜 • T.toLinearMap.svdRight i :=
    (T.toLinearMap.svdRight.sum_repr' x).symm
  have hT : T x = T.toLinearMap x := rfl
  conv_rhs => rw [hx]
  simp only [coe_comp', Function.comp_apply, map_sum, map_smul,
    absoluteValue_apply_svdRight, polarPart_apply_svdRight, smul_smul]
  rw [hT, T.toLinearMap.svd_apply x]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_smul, mul_comm]

/-- `|T|` is a positive operator. -/
theorem absoluteValue_isPositive : T.absoluteValue.IsPositive := by
  rw [absoluteValue_eq_sum]
  refine isPositive_sum _ fun i _ ↦ ?_
  apply IsPositive.smul_of_nonneg
  · exact isPositive_rankOne_self _
  · exact_mod_cast T.toLinearMap.singularValues_nonneg i.val

/-- `|T|` is self-adjoint: `|T|† = |T|`. -/
theorem adjoint_absoluteValue [CompleteSpace E] : adjoint T.absoluteValue = T.absoluteValue :=
  T.absoluteValue_isPositive.isSelfAdjoint.adjoint_eq

/-- The canonical characterization of `|T|`: `|T|² = T† ∘L T`. -/
theorem absoluteValue_sq [CompleteSpace E] [CompleteSpace F] :
    T.absoluteValue ∘L T.absoluteValue = T† ∘L T := by
  ext x
  have hx : x = ∑ i, ⟪T.toLinearMap.svdRight i, x⟫_𝕜 • T.toLinearMap.svdRight i :=
    (T.toLinearMap.svdRight.sum_repr' x).symm
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp only [coe_comp', Function.comp_apply, map_sum, map_smul,
    absoluteValue_apply_svdRight, adjoint_comp_self_apply_svdRight, smul_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring_nf

section UniquenessFoundations

variable [CompleteSpace E] [CompleteSpace F]

/-- For a partial isometry `U` (`U ∘ U† ∘ U = U`), the operator `U† ∘ U` acts as the identity on
`(ker U)ᗮ`. This is the fixed-point form of the partial-isometry projection property: `U† ∘ U`
is the orthogonal projection onto `(ker U)ᗮ`. -/
theorem adjoint_apply_apply_of_partialIsometry_of_mem_orthogonal_ker
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    [CompleteSpace G] {U : E →L[𝕜] G} (hU : U ∘L U.adjoint ∘L U = U) {y : E}
    (hy : y ∈ (LinearMap.ker U.toLinearMap)ᗮ) :
    U.adjoint (U y) = y := by
  have hUd : U.adjoint ∘L U ∘L U.adjoint = U.adjoint := by
    have h := congr_arg ContinuousLinearMap.adjoint hU
    simpa [adjoint_comp] using h
  rw [LinearMap.orthogonal_ker] at hy
  obtain ⟨z, hz⟩ := hy
  -- LinearMap.adjoint U.toLinearMap and ContinuousLinearMap.adjoint U agree on application.
  have hz' : U.adjoint z = y := hz
  rw [← hz']
  have heq : (U.adjoint ∘L U ∘L U.adjoint) z = U.adjoint z := by rw [hUd]
  simpa [coe_comp', Function.comp_apply] using heq

omit [CompleteSpace E] [CompleteSpace F] in
/-- For `x ∈ ker (absoluteValue T)` and `i` a non-zero-singular-value index, `⟪svdRight i, x⟫ = 0`.
The right singular vectors with non-zero singular values are orthogonal to the kernel of `|T|`. -/
theorem inner_svdRight_eq_zero_of_absoluteValue_apply_eq_zero
    {x : E} (hx : T.absoluteValue x = 0) {i : Fin (finrank 𝕜 E)}
    (hσ : T.toLinearMap.singularValues i.val ≠ 0) :
    ⟪T.toLinearMap.svdRight i, x⟫_𝕜 = 0 := by
  have h0 : ⟪T.toLinearMap.svdRight i, T.absoluteValue x⟫_𝕜 = 0 := by
    rw [hx, inner_zero_right]
  rw [← T.absoluteValue_isPositive.inner_left_eq_inner_right, absoluteValue_apply_svdRight,
    inner_smul_left, RCLike.conj_ofReal] at h0
  rcases mul_eq_zero.mp h0 with hσ' | h
  · exact absurd (by exact_mod_cast hσ' : T.toLinearMap.singularValues i.val = 0) hσ
  · exact h

omit [CompleteSpace E] [CompleteSpace F] in
/-- The polar part vanishes on the kernel of the absolute value: `|T| x = 0 → polarPart T x = 0`. -/
theorem polarPart_apply_eq_zero_of_absoluteValue_apply_eq_zero
    {x : E} (hx : T.absoluteValue x = 0) : T.polarPart x = 0 := by
  rw [polarPart_eq_sum, ContinuousLinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [rankOne_apply]
  by_cases hσ : T.toLinearMap.singularValues i.val = 0
  · rw [T.toLinearMap.svdLeft_eq_zero_of_singularValues_eq_zero i hσ, smul_zero]
  · rw [T.inner_svdRight_eq_zero_of_absoluteValue_apply_eq_zero hx hσ, zero_smul]

omit [CompleteSpace E] [CompleteSpace F] in
/-- For any factorization `T = U ∘L absoluteValue T`, the action on right singular vectors is `T
(svdRight i) = σᵢ • U (svdRight i)`. -/
theorem apply_svdRight_of_eq_comp_absoluteValue {U : E →L[𝕜] F}
    (hU : T = U ∘L T.absoluteValue) (i : Fin (finrank 𝕜 E)) :
    T (T.toLinearMap.svdRight i) =
      (T.toLinearMap.singularValues i.val : 𝕜) • U (T.toLinearMap.svdRight i) := by
  have h := DFunLike.congr_fun hU (T.toLinearMap.svdRight i)
  rwa [ContinuousLinearMap.comp_apply, T.absoluteValue_apply_svdRight,
    ContinuousLinearMap.map_smul] at h

/-- **Uniqueness of the positive square root of `T† ∘L T`**. -/
theorem absoluteValue_eq_of_isPositive_sq {P : E →L[𝕜] E} (hP : P.IsPositive)
    (h : P ∘L P = T.adjoint ∘L T) : P = T.absoluteValue := by
  apply ContinuousLinearMap.coe_injective
  apply Basis.ext T.toLinearMap.svdRight.toBasis
  intro i
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
  have h_sq : T.absoluteValue ∘L T.absoluteValue = P ∘L P := T.absoluteValue_sq.trans h.symm
  rw [hP.apply_eq_of_isPositive_sq_apply_eq h_sq (T.toLinearMap.singularValues_nonneg i.val)
      (T.absoluteValue_apply_svdRight i), ← T.absoluteValue_apply_svdRight i]

/-- **Polar decomposition uniqueness.** -/
theorem polar_decomposition_unique {P' : E →L[𝕜] E} {U' : E →L[𝕜] F}
    (hT : T = U' ∘L P') (hP' : P'.IsPositive)
    (hU' : U' ∘L U'.adjoint ∘L U' = U')
    (hker : LinearMap.ker U'.toLinearMap = LinearMap.ker P'.toLinearMap) :
    P' = T.absoluteValue ∧ U' = T.polarPart := by
  -- Step 1: T† ∘L T = P' ∘L P' (using partial-isometry on range P').
  have hTT : T.adjoint ∘L T = P' ∘L P' := by
    rw [hT, ContinuousLinearMap.adjoint_comp, hP'.isSelfAdjoint.adjoint_eq]
    ext y
    simp only [ContinuousLinearMap.comp_apply]
    have hP'y : P' y ∈ (LinearMap.ker U'.toLinearMap)ᗮ := by
      rw [hker, ← hP'.isSymmetric.range_eq_orthogonal_ker]
      exact ⟨y, rfl⟩
    rw [adjoint_apply_apply_of_partialIsometry_of_mem_orthogonal_ker hU' hP'y]
  -- Step 2: P' = absoluteValue T (uniqueness of the positive square root of `T† ∘L T`).
  have habs : P' = T.absoluteValue := T.absoluteValue_eq_of_isPositive_sq hP' hTT.symm
  -- Step 3: U' = polarPart T (using ker U' = ker P' = ker absoluteValue T = ker polarPart T).
  have hU : U' = T.polarPart := by
    apply ContinuousLinearMap.coe_injective
    apply Basis.ext T.toLinearMap.svdRight.toBasis
    intro i
    simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
    by_cases hσ : T.toLinearMap.singularValues i.val = 0
    · -- σᵢ = 0: both U' and polarPart T vanish on svdRight i (via ker chain).
      have habs_z : T.absoluteValue (T.toLinearMap.svdRight i) = 0 := by
        rw [T.absoluteValue_apply_svdRight i, hσ, RCLike.ofReal_zero, zero_smul]
      -- ker chain: T.absoluteValue → P' (via habs) → U' (via hker).
      have hU'_z : U' (T.toLinearMap.svdRight i) = 0 := by
        rw [← ContinuousLinearMap.mem_ker, hker]
        exact habs.symm ▸ habs_z
      rw [hU'_z, T.polarPart_apply_eq_zero_of_absoluteValue_apply_eq_zero habs_z]
    · -- σᵢ ≠ 0: T u = σᵢ • U' u = σᵢ • polarPart T u via apply_svdRight_of_eq_comp_absoluteValue.
      have hT_apply := T.apply_svdRight_of_eq_comp_absoluteValue (habs ▸ hT) i
      have hT_apply' := T.apply_svdRight_of_eq_comp_absoluteValue T.polar_decomposition i
      have hσ' : (T.toLinearMap.singularValues i.val : 𝕜) ≠ 0 := by exact_mod_cast hσ
      exact smul_right_injective F hσ' (hT_apply.symm.trans hT_apply')
  exact ⟨habs, hU⟩

end UniquenessFoundations

end ContinuousLinearMap
