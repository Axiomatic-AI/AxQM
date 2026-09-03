/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.PiTensorProductMap
public import AxQM.ToMathlib.Analysis.InnerProductSpace.CFC
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Density

/-!
# The n-ary tensor map preserves positivity and density operators

For a finite family of positive (resp. density) operators, the n-ary tensor map
`PiTensorProduct.mapCLM` produces a positive (resp. density) operator.

## Main results

* `PiTensorProduct.mapCLM_isDensityOp` — `⨂ᵢ ρᵢ` is a density operator when each `ρᵢ` is.
-/

@[expose] public section

namespace PiTensorProduct

variable {ι : Type*} [Finite ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, FiniteDimensional ℂ (E i)] [∀ i, CompleteSpace (E i)]

/-- **The n-ary tensor map preserves positivity**: if each `f i` is positive, so is `mapCLM f`. -/
theorem mapCLM_isPositive {f : ∀ i, E i →L[ℂ] E i} (h : ∀ i, (f i).IsPositive) :
    (mapCLM f).IsPositive := by
  have key : mapCLM f =
      (ContinuousLinearMap.adjoint (mapCLM fun i ↦ CFC.sqrt (f i))).comp
        (mapCLM fun i ↦ CFC.sqrt (f i)) := by
    rw [mapCLM_adjoint, ← mapCLM_comp]
    congr 1
    funext i
    have hnn : (0 : E i →L[ℂ] E i) ≤ f i := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (h i)
    have hadj : ContinuousLinearMap.adjoint (CFC.sqrt (f i)) = CFC.sqrt (f i) := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg (f i))).isSelfAdjoint
    rw [hadj, ← ContinuousLinearMap.mul_def]
    exact (CFC.sqrt_mul_sqrt_self (f i) hnn).symm
  rw [key]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- **The n-ary tensor map preserves density operators**: `⨂ᵢ ρᵢ` is a density operator when each `ρ
i` is. -/
theorem mapCLM_isDensityOp {f : ∀ i, E i →L[ℂ] E i} (h : ∀ i, (f i).IsDensityOp) :
    (mapCLM f).IsDensityOp := by
  haveI := Fintype.ofFinite ι
  refine ⟨mapCLM_isPositive fun i ↦ (h i).1, ?_⟩
  rw [mapCLM_trace]
  exact Finset.prod_eq_one fun i _ ↦ (h i).2

end PiTensorProduct
