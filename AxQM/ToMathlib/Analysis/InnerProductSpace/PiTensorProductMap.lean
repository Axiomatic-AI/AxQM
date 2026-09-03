/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.PiTensorProduct
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The n-ary tensor map on inner product spaces and its adjoint

For a finite family of continuous linear maps `f i : E i →L[𝕜] E' i` between finite-dimensional
inner product spaces, `PiTensorProduct.mapCLM f : (⨂ᵢ Eᵢ) →L[𝕜] ⨂ᵢ E'ᵢ` is the induced
continuous linear map, `⨂ aᵢ ↦ ⨂ (f i) aᵢ`.

## Main results

* `PiTensorProduct.mapCLM` — the induced continuous linear map.
* `PiTensorProduct.mapCLM_adjoint` — `(mapCLM f)† = mapCLM (fun i ↦ (f i)†)`.
* `PiTensorProduct.mapCLM_trace` — `Tr (mapCLM f) = ∏ᵢ Tr (f i)`.
-/

@[expose] public section

namespace PiTensorProduct

open scoped TensorProduct InnerProductSpace

variable {ι : Type*} [Finite ι] {𝕜 : Type*} [RCLike 𝕜]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
    [∀ i, FiniteDimensional 𝕜 (E i)]

instance instFiniteDimensionalPiTensor : FiniteDimensional 𝕜 (⨂[𝕜] i, E i) :=
  Module.Basis.finiteDimensional_of_finite (Basis.piTensorProduct fun i ↦ Module.finBasis 𝕜 (E i))

instance instCompleteSpacePiTensor : CompleteSpace (⨂[𝕜] i, E i) :=
  FiniteDimensional.complete 𝕜 _

variable {E' : ι → Type*} [∀ i, NormedAddCommGroup (E' i)] [∀ i, InnerProductSpace 𝕜 (E' i)]
  [∀ i, FiniteDimensional 𝕜 (E' i)]

/-- **The n-ary tensor map** `⨂ aᵢ ↦ ⨂ (f i) aᵢ` as a continuous linear map on the inner-product
tensor products. -/
noncomputable def mapCLM (f : ∀ i, E i →L[𝕜] E' i) : (⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i :=
  LinearMap.toContinuousLinearMap (PiTensorProduct.map fun i ↦ (f i : E i →ₗ[𝕜] E' i))

omit [∀ i, FiniteDimensional 𝕜 (E' i)] in
@[simp]
theorem mapCLM_tprod (f : ∀ i, E i →L[𝕜] E' i) (x : ∀ i, E i) :
    mapCLM f (⨂ₜ[𝕜] i, x i) = ⨂ₜ[𝕜] i, f i (x i) := by
  simp [mapCLM, PiTensorProduct.map_tprod]

/-- **The adjoint of the n-ary tensor map is the n-ary tensor map of the adjoints:** `(mapCLM f)† =
mapCLM (fun i ↦ (f i)†)`. -/
theorem mapCLM_adjoint [∀ i, CompleteSpace (E i)] [∀ i, CompleteSpace (E' i)]
    (f : ∀ i, E i →L[𝕜] E' i) :
    ContinuousLinearMap.adjoint (mapCLM f) =
      mapCLM (fun i ↦ ContinuousLinearMap.adjoint (f i)) := by
  haveI := Fintype.ofFinite ι
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      simp only [map_smul, inner_smul_left, inner_smul_right, mapCLM_tprod, inner_tprod_tprod]
      congr 2
      exact Finset.prod_congr rfl fun i _ ↦
        ContinuousLinearMap.adjoint_inner_left (f i) (b i) (a i)
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, inner_add_right, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, inner_add_left, hx₁, hx₂]

/-- **The trace of the n-ary tensor map is the product of the factor traces:** `Tr (mapCLM f) = ∏ᵢ
Tr (f i)`. -/
-- `[Fintype ι]` rather than the file's `[Finite ι]`: the `∏ i` in the statement needs it at
-- elaboration time.
theorem mapCLM_trace [Fintype ι] (f : ∀ i, E i →L[𝕜] E i) :
    LinearMap.trace 𝕜 (⨂[𝕜] i, E i) (mapCLM f).toLinearMap =
      ∏ i, LinearMap.trace 𝕜 (E i) (f i).toLinearMap := by
  classical
  rw [LinearMap.trace_eq_sum_inner _
    (OrthonormalBasis.piTensorProduct fun i ↦ stdOrthonormalBasis 𝕜 (E i))]
  simp_rw [fun i ↦ LinearMap.trace_eq_sum_inner (f i).toLinearMap (stdOrthonormalBasis 𝕜 (E i))]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr Fintype.piFinset_univ.symm fun p _ ↦ ?_
  rw [OrthonormalBasis.piTensorProduct_apply, ContinuousLinearMap.coe_coe, mapCLM_tprod,
    inner_tprod_tprod]
  simp only [ContinuousLinearMap.coe_coe]

variable {E'' : ι → Type*} [∀ i, NormedAddCommGroup (E'' i)] [∀ i, InnerProductSpace 𝕜 (E'' i)]
  [∀ i, FiniteDimensional 𝕜 (E'' i)]

omit [∀ i, FiniteDimensional 𝕜 (E'' i)] in
theorem mapCLM_comp (g : ∀ i, E' i →L[𝕜] E'' i) (f : ∀ i, E i →L[𝕜] E' i) :
    mapCLM (fun i ↦ (g i).comp (f i)) = (mapCLM g).comp (mapCLM f) := by
  ext x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a => simp
  | add x y hx hy => simp [hx, hy]

end PiTensorProduct
