/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import AxQM.ToMathlib.Analysis.InnerProductSpace.HSPairing
public import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Matricization (vectorization) on a tensor product

The vectorization isomorphism `matricize b : E ⊗[𝕜] F ≃ₗ[𝕜] (F →L[𝕜] E)`,
parametrized by an orthonormal basis `b` on the right factor `F`. It reshapes a bipartite
vector `Ψ : E ⊗[𝕜] F` into a continuous linear map by
`matricize b Ψ φ = ∑ k, ⟪b k, φ⟫_𝕜 • restrictRight b k Ψ`. The canonical bridge between
Schmidt decomposition (a "vectorized" state on the bipartite space) and the SVD of an
operator (the same data viewed as a linear map).

## Main definitions

- `TensorProduct.matricize` : the basis-parametric `LinearEquiv`
  `E ⊗[𝕜] F ≃ₗ[𝕜] (F →L[𝕜] E)`.
-/

@[expose] public section

namespace OrthonormalBasis

open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι]
  {𝕜 : Type*} [RCLike 𝕜]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Basis-orthonormality `δ`-collapse (summed-index on the LEFT of the inner product):
`∑ k, ⟪b k, b ℓ⟫_𝕜 • f k = f ℓ`. -/
theorem sum_inner_basis_smul_left {G : Type*} [AddCommMonoid G] [Module 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 F) (f : ι → G) (ℓ : ι) :
    ∑ k, ⟪b k, b ℓ⟫_𝕜 • f k = f ℓ := by
  classical
  rw [Finset.sum_eq_single ℓ (fun k _ hk ↦ by rw [b.inner_eq_ite, if_neg hk, zero_smul])
    (fun h ↦ absurd (Finset.mem_univ ℓ) h), b.inner_eq_ite, if_pos rfl, one_smul]

/-- Basis-orthonormality `δ`-collapse (summed-index on the RIGHT of the inner product):
`∑ k, ⟪b ℓ, b k⟫_𝕜 • f k = f ℓ`. -/
theorem sum_inner_basis_smul_right {G : Type*} [AddCommMonoid G] [Module 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 F) (f : ι → G) (ℓ : ι) :
    ∑ k, ⟪b ℓ, b k⟫_𝕜 • f k = f ℓ := by
  classical
  rw [Finset.sum_eq_single ℓ
    (fun k _ hk ↦ by rw [b.inner_eq_ite, if_neg (Ne.symm hk), zero_smul])
    (fun h ↦ absurd (Finset.mem_univ ℓ) h), b.inner_eq_ite, if_pos rfl, one_smul]

end OrthonormalBasis

namespace TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {ι : Type*} [Fintype ι]

open scoped InnerProductSpace

/-- The forward `LinearMap` of `TensorProduct.matricize`. -/
noncomputable def matricizeToCLM (b : OrthonormalBasis ι 𝕜 F) :
    E ⊗[𝕜] F →ₗ[𝕜] (F →L[𝕜] E) where
  toFun Ψ := ∑ k : ι, (innerSL 𝕜 (b k)).smulRight (LinearMap.restrictRight b k Ψ)
  map_add' Ψ₁ Ψ₂ := by
    ext φ
    simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, Finset.sum_add_distrib, smul_add]
  map_smul' c Ψ := by
    ext φ
    simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, Finset.smul_sum, smul_smul, mul_comm]

@[simp]
theorem matricizeToCLM_apply (b : OrthonormalBasis ι 𝕜 F) (Ψ : E ⊗[𝕜] F) (φ : F) :
    matricizeToCLM b Ψ φ = ∑ k : ι, ⟪b k, φ⟫_𝕜 • LinearMap.restrictRight b k Ψ := by
  simp [matricizeToCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply]

/-- The inverse `LinearMap` of `TensorProduct.matricize`: `T ↦ ∑ k, T (b k) ⊗ₜ b k`. -/
noncomputable def matricizeFromCLM (b : OrthonormalBasis ι 𝕜 F) :
    (F →L[𝕜] E) →ₗ[𝕜] E ⊗[𝕜] F where
  toFun T := ∑ k : ι, T (b k) ⊗ₜ[𝕜] b k
  map_add' T₁ T₂ := by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c T := by simp [TensorProduct.smul_tmul', Finset.smul_sum]

@[simp]
theorem matricizeFromCLM_apply (b : OrthonormalBasis ι 𝕜 F) (T : F →L[𝕜] E) :
    matricizeFromCLM b T = ∑ k : ι, T (b k) ⊗ₜ[𝕜] b k :=
  rfl

/-- `matricizeToCLM b` post-composed with `matricizeFromCLM b` is the identity on
`F →L[𝕜] E`. The right-inverse half of `TensorProduct.matricize` below. -/
theorem matricizeToCLM_comp_matricizeFromCLM (b : OrthonormalBasis ι 𝕜 F) :
    (matricizeToCLM (E := E) b).comp (matricizeFromCLM b) = LinearMap.id :=
  LinearMap.ext fun T ↦ ContinuousLinearMap.ext fun φ ↦ by
    have inner_collapse : ∀ ℓ, LinearMap.restrictRight b ℓ (∑ k, T (b k) ⊗ₜ[𝕜] b k)
        = T (b ℓ) := fun ℓ ↦ by
      rw [map_sum]
      simp_rw [LinearMap.restrictRight_tmul]
      exact b.sum_inner_basis_smul_right (T ∘ b) ℓ
    simp only [LinearMap.coe_comp, Function.comp_apply, matricizeFromCLM_apply,
      matricizeToCLM_apply, LinearMap.id_coe, id_eq]
    simp_rw [inner_collapse, ← T.map_smul, ← map_sum, b.sum_repr']

/-- `matricizeFromCLM b` post-composed with `matricizeToCLM b` is the identity on
`E ⊗[𝕜] F`. The left-inverse half of `TensorProduct.matricize` below. -/
theorem matricizeFromCLM_comp_matricizeToCLM (b : OrthonormalBasis ι 𝕜 F) :
    (matricizeFromCLM b).comp (matricizeToCLM (E := E) b) = LinearMap.id :=
  LinearMap.ext fun Ψ ↦ by
    simp only [LinearMap.coe_comp, Function.comp_apply, matricizeFromCLM_apply,
      matricizeToCLM_apply, LinearMap.id_coe, id_eq]
    conv_rhs => rw [← LinearMap.sum_embedRight_restrictRight_eq_self b Ψ]
    exact Finset.sum_congr rfl fun k _ ↦ by
      rw [LinearMap.embedRight_apply,
        b.sum_inner_basis_smul_left (LinearMap.restrictRight b · Ψ)]

/-- **Abstract matricization (bra-ket isomorphism)**, basis-parametric on the F-side. For an
orthonormal basis `b : OrthonormalBasis ι 𝕜 F`, this `LinearEquiv` identifies `Ψ : E ⊗[𝕜] F`
with the continuous linear map `F →L[𝕜] E` characterized by

`matricize b Ψ φ = ∑ k, ⟪b k, φ⟫_𝕜 • restrictRight b k Ψ`,

i.e., the basis-defined bilinear pairing on `F` (the inner product is sesquilinear, but indexing
by the orthonormal basis turns it into a linear pairing on coordinates) applied slot-by-slot.
The inverse sends a CLM `T : F →L[𝕜] E` to the bipartite vector `∑ k, T (b k) ⊗ₜ b k`.
-/
noncomputable def matricize (b : OrthonormalBasis ι 𝕜 F) :
    E ⊗[𝕜] F ≃ₗ[𝕜] (F →L[𝕜] E) :=
  LinearEquiv.ofLinear (matricizeToCLM b) (matricizeFromCLM b)
    (matricizeToCLM_comp_matricizeFromCLM b)
    (matricizeFromCLM_comp_matricizeToCLM b)

end TensorProduct
