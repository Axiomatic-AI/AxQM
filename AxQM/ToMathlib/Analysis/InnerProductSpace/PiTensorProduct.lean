/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import AxQM.ToMathlib.LinearAlgebra.PiTensorProduct.Finiteness
public import AxQM.ToMathlib.Analysis.RCLike.Basic
public import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!

# Inner product space structure on `PiTensorProduct`

This file provides the inner product space structure on the n-ary tensor product
`⨂[𝕜] i, s i` of inner product spaces.

## Main definitions

* `PiTensorProduct.instNormedAddCommGroup`: the normed additive group structure on the n-ary
  tensor product, induced by the inner product.
* `PiTensorProduct.instInnerProductSpace`: the inner product space structure on the n-ary
  tensor product, where `⟪⨂ₜ a_i, ⨂ₜ b_i⟫ = ∏ i, ⟪a_i, b_i⟫`.
* `PiTensorProduct.reindexₗᵢ`: the linear isometry equivalence version of
  `PiTensorProduct.reindex`, re-indexing the tensor factors along an index equivalence.
* `PiTensorProduct.tmulEquivₗᵢ`, `PiTensorProduct.subsingletonEquivₗᵢ`: the linear isometry
  equivalence versions of `PiTensorProduct.tmulEquiv` (splitting the index type along `ι ⊕ ι₂`)
  and `PiTensorProduct.subsingletonEquiv` (a tensor power over a subsingleton index).
* `PiTensorProduct.tmulEquivDepₗᵢ`: the linear isometry equivalence version of
  `PiTensorProduct.tmulEquivDep` (splitting the index type along `ι ⊕ ι₂`), for a dependent
  family `N : ι ⊕ ι₂ → Type*` of inner product spaces.
* `PiTensorProduct.consEquivₗᵢ`: the linear isometry equivalence peeling the head factor off a
  tensor power `⨂[𝕜] (_ : Fin (n + 1)), M ≃ₗᵢ M ⊗[𝕜] (⨂[𝕜] (_ : Fin n), M)`.
-/

@[expose] public section

variable {ι : Type*} [Finite ι] {𝕜 : Type*} [RCLike 𝕜] {s : ι → Type*}
  [∀ i, NormedAddCommGroup (s i)] [∀ i, InnerProductSpace 𝕜 (s i)]

open scoped TensorProduct ComplexOrder
open Module

namespace PiTensorProduct

set_option backward.privateInPublic true in
/-- Sesquilinear map for the inner product on `⨂[𝕜] i, s i`.
On pure tensors: `inner_ (⨂ₜ a_i) (⨂ₜ b_i) = ∏ i, ⟪a_i, b_i⟫`. -/
private noncomputable abbrev inner_ : (⨂[𝕜] i, s i) →ₗ⋆[𝕜] (⨂[𝕜] i, s i) →ₗ[𝕜] 𝕜 :=
  dualDistrib ∘ₛₗ map (fun _ ↦ innerₛₗ 𝕜)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
noncomputable instance instInner : Inner 𝕜 (⨂[𝕜] i, s i) := ⟨fun x y ↦ inner_ x y⟩

private lemma inner_def (x y : ⨂[𝕜] i, s i) : inner 𝕜 x y = inner_ x y := rfl

variable (𝕜) in
@[simp] theorem inner_tprod_tprod [Fintype ι] (a b : Π i, s i) :
    inner 𝕜 (⨂ₜ[𝕜] i, a i) (⨂ₜ[𝕜] i, b i) = ∏ i, inner 𝕜 (a i) (b i) := by
  simp [inner_def, inner_, dualDistrib_apply, innerₛₗ_apply_apply]

set_option backward.privateInPublic true in
private theorem conj_inner_symm_aux (x y : ⨂[𝕜] i, s i) :
    (starRingEnd 𝕜) (inner 𝕜 x y) = inner 𝕜 y x := by
  haveI := Fintype.ofFinite ι
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' b =>
      rw [inner_def, inner_def]
      simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
      simp_rw [← inner_def]
      rw [inner_tprod_tprod, inner_tprod_tprod]
      simp only [map_mul, map_prod, starRingEnd_self_apply]
      simp_rw [← inner_conj_symm (𝕜 := 𝕜) (a _) (b _)]
      simp only [starRingEnd_self_apply]
      ring
    | add u v hu hv =>
      simp only [inner_def, map_add, LinearMap.add_apply] at hu hv ⊢
      rw [hu, hv]
  | add u v hu hv =>
    simp only [inner_def, map_add, LinearMap.add_apply] at hu hv ⊢
    rw [hu, hv]

/-- Helper: expand `inner 𝕜 x x` for a vector `x = mapIncl M' y` lying in the image of
a finite-dimensional sub-`PiTensorProduct`, in terms of an orthonormal basis on each `M' i`. -/
private theorem inner_self_eq_basis_sum [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] (M' : Π i, Submodule 𝕜 (s i))
    (b : Π i, OrthonormalBasis (κ i) 𝕜 (M' i)) (y : ⨂[𝕜] i, M' i) :
    inner 𝕜 (mapIncl M' y) (mapIncl M' y) =
      ∑ p : Π i, κ i, ‖(Basis.piTensorProduct fun i ↦ (b i).toBasis).repr y p‖ ^ 2 := by
  set B := Basis.piTensorProduct (fun i ↦ (b i).toBasis) with hB
  have hy : y = ∑ p : Π i, κ i, B.repr y p • B p := (B.sum_repr y).symm
  conv_lhs => rw [hy]
  rw [inner_def, map_sum]
  simp only [LinearMap.sum_apply, map_sum, map_smulₛₗ, LinearMap.smul_apply,
    RingHom.id_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hsq : (algebraMap ℝ 𝕜) (‖B.repr y p‖ ^ 2) =
      B.repr y p * (starRingEnd 𝕜) (B.repr y p) :=
    RCLike.ofReal_norm_sq_eq_mul_conj _
  rw [hsq]
  classical
  have hBp : (mapIncl M') (B p) = ⨂ₜ[𝕜] i, ((b i) (p i) : s i) := by
    rw [hB, mapIncl, Basis.piTensorProduct_apply, map_tprod]; simp
  have hinner : ∀ q, inner_ ((mapIncl M') (B p)) ((mapIncl M') (B q)) =
      if p = q then 1 else 0 := by
    intro q
    have hBq : (mapIncl M') (B q) = ⨂ₜ[𝕜] i, ((b i) (q i) : s i) := by
      rw [hB, mapIncl, Basis.piTensorProduct_apply, map_tprod]; simp
    rw [← inner_def, hBp, hBq, inner_tprod_tprod]
    simp_rw [← Submodule.coe_inner, OrthonormalBasis.inner_eq_ite]
    rw [Fintype.prod_ite_zero]
    simp only [Finset.prod_const_one]
    congr 1
    exact propext (funext_iff (f := p) (g := q)).symm
  simp_rw [hinner, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ p)]

set_option backward.privateInPublic true in
private theorem inner_definite (x : ⨂[𝕜] i, s i) (hx : inner 𝕜 x x = 0) : x = 0 := by
  haveI := Fintype.ofFinite ι
  classical
  obtain ⟨M', hM', hsub⟩ :=
    exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨y, rfl⟩ := Set.singleton_subset_iff.mp hsub
  haveI : ∀ i, FiniteDimensional 𝕜 (M' i) := hM'
  let b : Π i, OrthonormalBasis (Fin (Module.finrank 𝕜 (M' i))) 𝕜 (M' i) :=
    fun i ↦ stdOrthonormalBasis 𝕜 (M' i)
  set B := Basis.piTensorProduct (fun i ↦ (b i).toBasis) with hB
  rw [inner_self_eq_basis_sum M' b y, ← hB, RCLike.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _] at hx
  have hzero : ∀ p, B.repr y p = 0 := fun p ↦ by
    have := hx p (Finset.mem_univ p)
    simpa [pow_eq_zero_iff] using this
  have hy : y = 0 := by simp [B.ext_elem_iff, hzero]
  rw [hy, map_zero]

set_option backward.privateInPublic true in
private protected theorem re_inner_self_nonneg (x : ⨂[𝕜] i, s i) :
    0 ≤ RCLike.re (inner 𝕜 x x) := by
  haveI := Fintype.ofFinite ι
  classical
  obtain ⟨M', hM', hsub⟩ :=
    exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨y, rfl⟩ := Set.singleton_subset_iff.mp hsub
  haveI : ∀ i, FiniteDimensional 𝕜 (M' i) := hM'
  let b : Π i, OrthonormalBasis (Fin (Module.finrank 𝕜 (M' i))) 𝕜 (M' i) :=
    fun i ↦ stdOrthonormalBasis 𝕜 (M' i)
  rw [inner_self_eq_basis_sum M' b y, RCLike.ofReal_re]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (⨂[𝕜] i, s i) :=
  letI : InnerProductSpace.Core 𝕜 (⨂[𝕜] i, s i) :=
    { conj_inner_symm := fun x y ↦ PiTensorProduct.conj_inner_symm_aux y x
      add_left _ _ _ := LinearMap.map_add₂ _ _ _ _
      smul_left _ _ _ := LinearMap.map_smulₛₗ₂ _ _ _ _
      definite := PiTensorProduct.inner_definite
      re_inner_nonneg := PiTensorProduct.re_inner_self_nonneg }
  this.toNormedAddCommGroup

noncomputable instance instInnerProductSpace : InnerProductSpace 𝕜 (⨂[𝕜] i, s i) := .ofCore _

section Reindex

variable {ι₂ : Type*} [Finite ι₂]

/-- Re-indexing the tensor factors along `e : ι ≃ ι₂` preserves the inner product:
`⟪reindex e x, reindex e y⟫ = ⟪x, y⟫`. -/
theorem inner_reindex_reindex (e : ι ≃ ι₂) (x y : ⨂[𝕜] i, s i) :
    inner 𝕜 (reindex 𝕜 s e x) (reindex 𝕜 s e y) = inner 𝕜 x y := by
  haveI := Fintype.ofFinite ι
  haveI := Fintype.ofFinite ι₂
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' b =>
      simp only [map_smul, inner_smul_left, inner_smul_right, reindex_tprod,
        inner_tprod_tprod]
      congr 2
      exact Equiv.prod_comp e.symm fun i ↦ inner 𝕜 (a i) (b i)
    | add u v hu hv =>
      simp only [map_add, inner_add_right] at hu hv ⊢
      rw [hu, hv]
  | add u v hu hv =>
    simp only [map_add, inner_add_left] at hu hv ⊢
    rw [hu, hv]

variable (𝕜 s) in
/-- Re-indexing the tensor factors along `e : ι ≃ ι₂` as a linear isometry equivalence.
This is the `≃ₗᵢ` version of the linear `PiTensorProduct.reindex`. -/
noncomputable def reindexₗᵢ (e : ι ≃ ι₂) :
    (⨂[𝕜] i, s i) ≃ₗᵢ[𝕜] ⨂[𝕜] i, s (e.symm i) :=
  (reindex 𝕜 s e).isometryOfInner (inner_reindex_reindex e)

@[simp] theorem reindexₗᵢ_toLinearEquiv (e : ι ≃ ι₂) :
    (reindexₗᵢ 𝕜 s e).toLinearEquiv = reindex 𝕜 s e := rfl

@[simp] theorem coe_reindexₗᵢ (e : ι ≃ ι₂) :
    ⇑(reindexₗᵢ 𝕜 s e) = reindex 𝕜 s e := rfl

@[simp] theorem reindexₗᵢ_tprod (e : ι ≃ ι₂) (f : Π i, s i) :
    reindexₗᵢ 𝕜 s e (⨂ₜ[𝕜] i, f i) = ⨂ₜ[𝕜] i, f (e.symm i) :=
  reindex_tprod e f

@[simp] theorem reindexₗᵢ_symm_toLinearEquiv (e : ι ≃ ι₂) :
    (reindexₗᵢ 𝕜 s e).symm.toLinearEquiv = (reindex 𝕜 s e).symm := rfl

theorem reindexₗᵢ_symm_const {M : Type*} [NormedAddCommGroup M] [InnerProductSpace 𝕜 M]
    (e : ι ≃ ι₂) : (reindexₗᵢ 𝕜 (fun _ ↦ M) e).symm = reindexₗᵢ 𝕜 (fun _ ↦ M) e.symm := by
  apply LinearIsometryEquiv.toLinearEquiv_injective
  rw [reindexₗᵢ_symm_toLinearEquiv, reindexₗᵢ_toLinearEquiv]
  exact reindex_symm e

end Reindex

section TmulEquiv

variable {ι₂ : Type*} [Finite ι₂] (M : Type*) [NormedAddCommGroup M] [InnerProductSpace 𝕜 M]

/-- Splitting the index type along `ι ⊕ ι₂` preserves the inner product:
`⟪tmulEquiv (a ⊗ b), tmulEquiv (c ⊗ d)⟫ = ⟪a ⊗ b, c ⊗ d⟫` on the `TensorProduct` of tensor
powers. -/
theorem inner_tmulEquiv_tmulEquiv (x y : (⨂[𝕜] (_ : ι), M) ⊗[𝕜] (⨂[𝕜] (_ : ι₂), M)) :
    inner 𝕜 (tmulEquiv 𝕜 M x) (tmulEquiv 𝕜 M y) = inner 𝕜 x y := by
  haveI := Fintype.ofFinite ι
  haveI := Fintype.ofFinite ι₂
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, inner_add_left, hu, hv]
  | tmul xι xι₂ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, inner_add_right, hu, hv]
    | tmul yι yι₂ =>
      induction xι using PiTensorProduct.induction_on with
      | smul_tprod r a =>
        induction xι₂ using PiTensorProduct.induction_on with
        | smul_tprod r' b =>
          induction yι using PiTensorProduct.induction_on with
          | smul_tprod t c =>
            induction yι₂ using PiTensorProduct.induction_on with
            | smul_tprod t' d =>
              simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul,
                inner_smul_left, inner_smul_right, tmulEquiv_apply, inner_tprod_tprod,
                _root_.TensorProduct.inner_tmul, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
              try ring
            | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, inner_add_right, hu, hv]
          | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, inner_add_right, hu, hv]
        | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, inner_add_left, hu, hv]
      | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, inner_add_left, hu, hv]

variable (𝕜) in
/-- Splitting the index type along `ι ⊕ ι₂` as a linear isometry equivalence.
This is the `≃ₗᵢ` version of the linear `PiTensorProduct.tmulEquiv` for a constant family. -/
noncomputable def tmulEquivₗᵢ :
    (⨂[𝕜] (_ : ι), M) ⊗[𝕜] (⨂[𝕜] (_ : ι₂), M) ≃ₗᵢ[𝕜] ⨂[𝕜] (_ : ι ⊕ ι₂), M where
  toLinearEquiv := tmulEquiv 𝕜 M
  norm_map' x := by
    rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜), norm_eq_sqrt_re_inner (𝕜 := 𝕜),
      inner_tmulEquiv_tmulEquiv M x x]

@[simp] theorem tmulEquivₗᵢ_toLinearEquiv :
    (tmulEquivₗᵢ 𝕜 M (ι := ι) (ι₂ := ι₂)).toLinearEquiv = tmulEquiv 𝕜 M := rfl

@[simp] theorem coe_tmulEquivₗᵢ :
    ⇑(tmulEquivₗᵢ 𝕜 M (ι := ι) (ι₂ := ι₂)) = tmulEquiv 𝕜 M := rfl

@[simp] theorem tmulEquivₗᵢ_tprod (a : ι → M) (b : ι₂ → M) :
    tmulEquivₗᵢ 𝕜 M ((⨂ₜ[𝕜] i, a i) ⊗ₜ[𝕜] (⨂ₜ[𝕜] i, b i)) = ⨂ₜ[𝕜] i, Sum.elim a b i :=
  tmulEquiv_apply 𝕜 M a b

@[simp] theorem tmulEquivₗᵢ_symm_tprod (a : ι ⊕ ι₂ → M) :
    (tmulEquivₗᵢ 𝕜 M).symm (⨂ₜ[𝕜] i, a i) =
      (⨂ₜ[𝕜] i, a (Sum.inl i)) ⊗ₜ[𝕜] (⨂ₜ[𝕜] i, a (Sum.inr i)) :=
  tmulEquiv_symm_apply 𝕜 M a

end TmulEquiv

section TmulEquivDep

variable {ι₂ : Type*} [Finite ι₂] (N : ι ⊕ ι₂ → Type*)
  [∀ i, NormedAddCommGroup (N i)] [∀ i, InnerProductSpace 𝕜 (N i)]

/-- Splitting the index type along `ι ⊕ ι₂` preserves the inner product, for a dependent family:
`⟪tmulEquivDep (a ⊗ b), tmulEquivDep (c ⊗ d)⟫ = ⟪a ⊗ b, c ⊗ d⟫` on the `TensorProduct` of tensor
powers over `N ∘ Sum.inl` and `N ∘ Sum.inr`. -/
theorem inner_tmulEquivDep_tmulEquivDep
    (x y : (⨂[𝕜] i, N (.inl i)) ⊗[𝕜] (⨂[𝕜] i, N (.inr i))) :
    inner 𝕜 (tmulEquivDep 𝕜 N x) (tmulEquivDep 𝕜 N y) = inner 𝕜 x y := by
  haveI := Fintype.ofFinite ι
  haveI := Fintype.ofFinite ι₂
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, inner_add_left, hu, hv]
  | tmul xι xι₂ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, inner_add_right, hu, hv]
    | tmul yι yι₂ =>
      induction xι using PiTensorProduct.induction_on with
      | smul_tprod r a =>
        induction xι₂ using PiTensorProduct.induction_on with
        | smul_tprod r' b =>
          induction yι using PiTensorProduct.induction_on with
          | smul_tprod t c =>
            induction yι₂ using PiTensorProduct.induction_on with
            | smul_tprod t' d =>
              rw [TensorProduct.inner_tmul, TensorProduct.smul_tmul_smul,
                TensorProduct.smul_tmul_smul]
              simp only [map_smul, map_mul, inner_smul_left, inner_smul_right,
                tmulEquivDep_apply, inner_tprod_tprod, Fintype.prod_sum_type]
              ring
            | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, inner_add_right, hu, hv]
          | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, inner_add_right, hu, hv]
        | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, inner_add_left, hu, hv]
      | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, inner_add_left, hu, hv]

variable (𝕜) in
/-- Splitting the index type along `ι ⊕ ι₂` as a linear isometry equivalence, for a dependent family
`N : ι ⊕ ι₂ → Type*`. This is the `≃ₗᵢ` version of the linear `PiTensorProduct.tmulEquivDep`.
-/
noncomputable def tmulEquivDepₗᵢ :
    (⨂[𝕜] i, N (.inl i)) ⊗[𝕜] (⨂[𝕜] i, N (.inr i)) ≃ₗᵢ[𝕜] ⨂[𝕜] i, N i where
  toLinearEquiv := tmulEquivDep 𝕜 N
  norm_map' x := by
    rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜), norm_eq_sqrt_re_inner (𝕜 := 𝕜),
      inner_tmulEquivDep_tmulEquivDep N x x]

@[simp] theorem tmulEquivDepₗᵢ_toLinearEquiv :
    (tmulEquivDepₗᵢ 𝕜 N).toLinearEquiv = tmulEquivDep 𝕜 N := rfl

@[simp] theorem coe_tmulEquivDepₗᵢ :
    ⇑(tmulEquivDepₗᵢ 𝕜 N) = tmulEquivDep 𝕜 N := rfl

@[simp] theorem tmulEquivDepₗᵢ_tprod (a : Π i, N (.inl i)) (b : Π i, N (.inr i)) :
    tmulEquivDepₗᵢ 𝕜 N ((⨂ₜ[𝕜] i, a i) ⊗ₜ[𝕜] (⨂ₜ[𝕜] i, b i)) = ⨂ₜ[𝕜] i, Sum.rec a b i :=
  tmulEquivDep_apply 𝕜 N a b

@[simp] theorem tmulEquivDepₗᵢ_symm_tprod (f : Π i, N i) :
    (tmulEquivDepₗᵢ 𝕜 N).symm (⨂ₜ[𝕜] i, f i) =
      (⨂ₜ[𝕜] i, f (.inl i)) ⊗ₜ[𝕜] (⨂ₜ[𝕜] i, f (.inr i)) :=
  tmulEquivDep_symm_apply 𝕜 N f

end TmulEquivDep

section Subsingleton

variable [Subsingleton ι] (i₀ : ι)

/-- On a subsingleton index type, the single-factor inner product is preserved:
`⟪subsingletonEquiv i₀ x, subsingletonEquiv i₀ y⟫ = ⟪x, y⟫`. -/
theorem inner_subsingletonEquiv_subsingletonEquiv (x y : ⨂[𝕜] i, s i) :
    inner 𝕜 (subsingletonEquiv i₀ x) (subsingletonEquiv i₀ y) = inner 𝕜 x y := by
  haveI := Fintype.ofFinite ι
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' b =>
      simp only [map_smul, inner_smul_left, inner_smul_right, subsingletonEquiv_apply_tprod,
        inner_tprod_tprod, Fintype.prod_subsingleton _ i₀]
    | add u v hu hv => simp only [map_add, inner_add_right, hu, hv]
  | add u v hu hv => simp only [map_add, inner_add_left, hu, hv]

variable (𝕜 s) in
/-- The tensor power over a subsingleton index type, as a linear isometry equivalence to the single
factor `s i₀`. This is the `≃ₗᵢ` version of the linear `PiTensorProduct.subsingletonEquiv`. -/
noncomputable def subsingletonEquivₗᵢ : (⨂[𝕜] i, s i) ≃ₗᵢ[𝕜] s i₀ :=
  (subsingletonEquiv i₀).isometryOfInner (inner_subsingletonEquiv_subsingletonEquiv i₀)

@[simp] theorem subsingletonEquivₗᵢ_toLinearEquiv :
    (subsingletonEquivₗᵢ 𝕜 s i₀).toLinearEquiv = subsingletonEquiv i₀ := rfl

@[simp] theorem coe_subsingletonEquivₗᵢ :
    ⇑(subsingletonEquivₗᵢ 𝕜 s i₀) = subsingletonEquiv i₀ := rfl

@[simp] theorem subsingletonEquivₗᵢ_tprod (f : Π i, s i) :
    subsingletonEquivₗᵢ 𝕜 s i₀ (⨂ₜ[𝕜] i, f i) = f i₀ :=
  subsingletonEquiv_apply_tprod i₀ f

end Subsingleton

section Congr

variable {t : ι → Type*} [∀ i, NormedAddCommGroup (t i)] [∀ i, InnerProductSpace 𝕜 (t i)]

/-- Applying a family of linear isometry equivalences factor-wise preserves the inner product:
`⟪congr e x, congr e y⟫ = ⟪x, y⟫`. -/
theorem inner_congr_congr (e : ∀ i, s i ≃ₗᵢ[𝕜] t i) (x y : ⨂[𝕜] i, s i) :
    inner 𝕜 (congr (fun i ↦ (e i).toLinearEquiv) x) (congr (fun i ↦ (e i).toLinearEquiv) y)
      = inner 𝕜 x y := by
  haveI := Fintype.ofFinite ι
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' b =>
      simp only [map_smul, inner_smul_left, inner_smul_right, congr_tprod, inner_tprod_tprod]
      congr 2
      exact Finset.prod_congr rfl fun i _ ↦ (e i).inner_map_map (a i) (b i)
    | add u v hu hv =>
      simp only [map_add, inner_add_right] at hu hv ⊢
      rw [hu, hv]
  | add u v hu hv =>
    simp only [map_add, inner_add_left] at hu hv ⊢
    rw [hu, hv]

variable (𝕜) in
/-- Applying a family of linear isometry equivalences factor-wise, as a linear isometry
equivalence `⨂[𝕜] i, s i ≃ₗᵢ ⨂[𝕜] i, t i`. The `≃ₗᵢ` version of `PiTensorProduct.congr`. -/
noncomputable def congrₗᵢ (e : ∀ i, s i ≃ₗᵢ[𝕜] t i) :
    (⨂[𝕜] i, s i) ≃ₗᵢ[𝕜] ⨂[𝕜] i, t i :=
  (congr (fun i ↦ (e i).toLinearEquiv)).isometryOfInner (inner_congr_congr e)

@[simp] theorem congrₗᵢ_toLinearEquiv (e : ∀ i, s i ≃ₗᵢ[𝕜] t i) :
    (congrₗᵢ 𝕜 e).toLinearEquiv = congr (fun i ↦ (e i).toLinearEquiv) := rfl

@[simp] theorem coe_congrₗᵢ (e : ∀ i, s i ≃ₗᵢ[𝕜] t i) :
    ⇑(congrₗᵢ 𝕜 e) = congr (fun i ↦ (e i).toLinearEquiv) := rfl

@[simp] theorem congrₗᵢ_tprod (e : ∀ i, s i ≃ₗᵢ[𝕜] t i) (f : ∀ i, s i) :
    congrₗᵢ 𝕜 e (⨂ₜ[𝕜] i, f i) = ⨂ₜ[𝕜] i, e i (f i) := by
  simp only [congrₗᵢ, LinearEquiv.coe_isometryOfInner, congr_tprod,
    LinearIsometryEquiv.coe_toLinearEquiv]

end Congr

section Cons

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] (n : ℕ)

/-- The index equivalence `Fin (n + 1) ≃ Fin 1 ⊕ Fin n` sending `0` to the left factor and each
`Fin.succ i` to the right factor. Used to peel the head factor off a tensor power. -/
def consSumEquiv : Fin (n + 1) ≃ Fin 1 ⊕ Fin n :=
  (finCongr (Nat.add_comm n 1)).trans finSumFinEquiv.symm

@[simp] theorem consSumEquiv_symm_inl (i : Fin 1) : (consSumEquiv n).symm (Sum.inl i) = 0 := by
  simp [consSumEquiv, Fin.ext_iff]

@[simp] theorem consSumEquiv_symm_inr (i : Fin n) :
    (consSumEquiv n).symm (Sum.inr i) = i.succ := by
  simp [consSumEquiv, finSumFinEquiv, Fin.succ]

variable (𝕜 M) in
/-- **Head-peel isometry**: peeling the first factor off a tensor power over `Fin (n + 1)`,
as a linear isometry equivalence
`⨂[𝕜] (_ : Fin (n + 1)), M ≃ₗᵢ M ⊗[𝕜] (⨂[𝕜] (_ : Fin n), M)`.
On pure tensors: `⨂ₜ f ↦ f 0 ⊗ₜ ⨂ₜ (f ∘ Fin.succ)`. -/
noncomputable def consEquivₗᵢ :
    (⨂[𝕜] (_ : Fin (n + 1)), M) ≃ₗᵢ[𝕜] M ⊗[𝕜] (⨂[𝕜] (_ : Fin n), M) :=
  (reindexₗᵢ 𝕜 (fun _ ↦ M) (consSumEquiv n)).trans
    ((tmulEquivₗᵢ 𝕜 M (ι := Fin 1) (ι₂ := Fin n)).symm.trans
      ((subsingletonEquivₗᵢ 𝕜 (fun _ ↦ M) (0 : Fin 1)).rTensor (⨂[𝕜] (_ : Fin n), M)))

@[simp] theorem consEquivₗᵢ_tprod (f : Fin (n + 1) → M) :
    consEquivₗᵢ 𝕜 M n (⨂ₜ[𝕜] i, f i) = f 0 ⊗ₜ[𝕜] (⨂ₜ[𝕜] i, f i.succ) := by
  simp only [consEquivₗᵢ, LinearIsometryEquiv.trans_apply, coe_reindexₗᵢ, reindex_tprod,
    tmulEquivₗᵢ_symm_tprod, LinearIsometryEquiv.rTensor_apply, LinearEquiv.rTensor_tmul,
    subsingletonEquivₗᵢ_toLinearEquiv, subsingletonEquiv_apply_tprod, consSumEquiv_symm_inl,
    consSumEquiv_symm_inr]

@[simp] theorem consEquivₗᵢ_symm_tmul (m : M) (g : Fin n → M) :
    (consEquivₗᵢ 𝕜 M n).symm (m ⊗ₜ[𝕜] (⨂ₜ[𝕜] i, g i)) =
      ⨂ₜ[𝕜] i, (Fin.cons m g : Fin (n + 1) → M) i := by
  apply (consEquivₗᵢ 𝕜 M n).injective
  rw [LinearIsometryEquiv.apply_symm_apply, consEquivₗᵢ_tprod, Fin.cons_zero]
  simp [Fin.cons_succ]

/-- Transport a factor along an index equality, as a linear isometry equivalence. -/
noncomputable def indexCastₗᵢ {ι' : Type*} {P : ι' → Type*}
    [∀ i, NormedAddCommGroup (P i)] [∀ i, InnerProductSpace 𝕜 (P i)] {a b : ι'} (h : a = b) :
    P a ≃ₗᵢ[𝕜] P b :=
  h ▸ LinearIsometryEquiv.refl 𝕜 (P a)

variable {N : Fin (n + 1) → Type*} [∀ i, NormedAddCommGroup (N i)]
  [∀ i, InnerProductSpace 𝕜 (N i)]

variable (𝕜 N) in
/-- **Dependent head-peel isometry**: peeling the first factor off a tensor power over `Fin (n + 1)`
for a dependent family `N`, as a linear isometry equivalence `⨂[𝕜] (i : Fin (n + 1)), N i ≃ₗᵢ N
0 ⊗[𝕜] (⨂[𝕜] (i : Fin n), N i.succ)`. -/
noncomputable def consEquivDepₗᵢ :
    (⨂[𝕜] (i : Fin (n + 1)), N i) ≃ₗᵢ[𝕜] N 0 ⊗[𝕜] (⨂[𝕜] (i : Fin n), N i.succ) :=
  (reindexₗᵢ 𝕜 N (consSumEquiv n)).trans
    ((tmulEquivDepₗᵢ 𝕜 (fun j ↦ N ((consSumEquiv n).symm j))).symm.trans
      (TensorProduct.congrIsometry
        ((subsingletonEquivₗᵢ 𝕜 (fun j ↦ N ((consSumEquiv n).symm (Sum.inl j))) 0).trans
          (indexCastₗᵢ (consSumEquiv_symm_inl n 0)))
        (congrₗᵢ 𝕜 (fun i ↦ indexCastₗᵢ (consSumEquiv_symm_inr n i)))))

@[simp] theorem indexCastₗᵢ_apply {ι' : Type*} {P : ι' → Type*}
    [∀ i, NormedAddCommGroup (P i)] [∀ i, InnerProductSpace 𝕜 (P i)] {a b : ι'} (h : a = b)
    (g : ∀ i, P i) : indexCastₗᵢ (𝕜 := 𝕜) h (g a) = g b := by subst h; rfl

variable (𝕜 N) in
@[simp] theorem consEquivDepₗᵢ_tprod (f : ∀ i, N i) :
    consEquivDepₗᵢ 𝕜 n N (⨂ₜ[𝕜] i, f i) = f 0 ⊗ₜ[𝕜] (⨂ₜ[𝕜] (i : Fin n), f i.succ) := by
  simp only [consEquivDepₗᵢ, LinearIsometryEquiv.trans_apply, coe_reindexₗᵢ, reindex_tprod,
    tmulEquivDepₗᵢ_symm_tprod, TensorProduct.congrIsometry_tmul, subsingletonEquivₗᵢ_tprod,
    congrₗᵢ_tprod, indexCastₗᵢ_apply]

variable (𝕜 N) in
@[simp] theorem consEquivDepₗᵢ_symm_tmul (m : N 0) (g : ∀ i : Fin n, N i.succ) :
    (consEquivDepₗᵢ 𝕜 n N).symm (m ⊗ₜ[𝕜] (⨂ₜ[𝕜] i, g i)) =
      ⨂ₜ[𝕜] i, (Fin.cons m g : ∀ i, N i) i := by
  apply (consEquivDepₗᵢ 𝕜 n N).injective
  rw [LinearIsometryEquiv.apply_symm_apply, consEquivDepₗᵢ_tprod, Fin.cons_zero]
  simp [Fin.cons_succ]

end Cons

end PiTensorProduct

section OrthonormalBasis

variable {κ : ι → Type*}

/-- The n-ary tensor of orthonormal families is orthonormal. -/
theorem Orthonormal.tprod {b : Π i, κ i → s i} (hb : ∀ i, Orthonormal 𝕜 (b i)) :
    Orthonormal 𝕜 fun p : Π i, κ i ↦ ⨂ₜ[𝕜] i, b i (p i) := by
  classical
  haveI := Fintype.ofFinite ι
  rw [orthonormal_iff_ite]
  intro p q
  rw [PiTensorProduct.inner_tprod_tprod]
  simp_rw [orthonormal_iff_ite.mp (hb _)]
  simp [Fintype.prod_ite_zero, ← funext_iff]

/-- The n-ary tensor of orthonormal bases gives an orthonormal family on the
`PiTensorProduct`. -/
theorem Orthonormal.basisPiTensorProduct {b : Π i, Basis (κ i) 𝕜 (s i)}
    (hb : ∀ i, Orthonormal 𝕜 (b i)) : Orthonormal 𝕜 (Basis.piTensorProduct b) := by
  haveI := Fintype.ofFinite ι
  convert Orthonormal.tprod hb using 1
  exact funext fun p ↦ Basis.piTensorProduct_apply b p

namespace OrthonormalBasis

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]

/-- The orthonormal basis of `⨂[𝕜] i, s i` from a family of orthonormal bases. -/
protected noncomputable def piTensorProduct (b : Π i, OrthonormalBasis (κ i) 𝕜 (s i)) :
    OrthonormalBasis (Π i, κ i) 𝕜 (⨂[𝕜] i, s i) :=
  (Basis.piTensorProduct (fun i ↦ (b i).toBasis)).toOrthonormalBasis
    (Orthonormal.basisPiTensorProduct (fun i ↦ (b i).orthonormal))

theorem piTensorProduct_eq (b : Π i, OrthonormalBasis (κ i) 𝕜 (s i)) :
    OrthonormalBasis.piTensorProduct b =
      (Basis.piTensorProduct (fun i ↦ (b i).toBasis)).toOrthonormalBasis
        (Orthonormal.basisPiTensorProduct (fun i ↦ (b i).orthonormal)) := rfl

@[simp]
lemma piTensorProduct_apply (b : Π i, OrthonormalBasis (κ i) 𝕜 (s i)) (p : Π i, κ i) :
    OrthonormalBasis.piTensorProduct b p = ⨂ₜ[𝕜] i, b i (p i) := by
  simp [piTensorProduct_eq, Module.Basis.coe_toOrthonormalBasis, Basis.piTensorProduct_apply]

@[simp]
lemma toBasis_piTensorProduct (b : Π i, OrthonormalBasis (κ i) 𝕜 (s i)) :
    (OrthonormalBasis.piTensorProduct b).toBasis =
      Basis.piTensorProduct (fun i ↦ (b i).toBasis) := by
  rw [piTensorProduct_eq, Module.Basis.toBasis_toOrthonormalBasis]

end OrthonormalBasis

end OrthonormalBasis
