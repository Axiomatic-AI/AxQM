/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Density

/-!
# Reduced states

The **reduced state** of a bipartite density operator `T : E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F` on the
factor `E` is its partial trace over `F`. This file records the basic fact that a reduced
state is again a density operator: tracing out a subsystem of a quantum state yields a
quantum state.

## Main results

* `ContinuousLinearMap.IsDensityOp.of_partialTraceRight_eq`,
  `ContinuousLinearMap.IsDensityOp.of_partialTraceLeft_eq`: a reduced state of a density
  operator is a density operator.
-/

@[expose] public section

open scoped TensorProduct

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {ι : Type*} [Fintype ι]

/-- **A reduced state is a density operator** (right factor). -/
theorem IsDensityOp.of_partialTraceRight_eq {T : E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F} {ρ : E →L[𝕜] E}
    (hT : T.IsDensityOp) (b : OrthonormalBasis ι 𝕜 F)
    (hρ : LinearMap.partialTraceRight b T.toLinearMap = ρ.toLinearMap) : ρ.IsDensityOp := by
  refine ⟨?_, ?_⟩
  · rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, ← hρ]
    exact LinearMap.partialTraceRight_isPositive b hT.isPositive.toLinearMap
  · rw [← hρ, LinearMap.trace_partialTraceRight]
    exact hT.trace_eq_one

/-- **A reduced state is a density operator** (left factor). -/
theorem IsDensityOp.of_partialTraceLeft_eq {T : E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F} {ρ : F →L[𝕜] F}
    (hT : T.IsDensityOp) (b : OrthonormalBasis ι 𝕜 E)
    (hρ : LinearMap.partialTraceLeft b T.toLinearMap = ρ.toLinearMap) : ρ.IsDensityOp := by
  refine ⟨?_, ?_⟩
  · rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, ← hρ]
    exact LinearMap.partialTraceLeft_isPositive b hT.isPositive.toLinearMap
  · rw [← hρ, LinearMap.trace_partialTraceLeft]
    exact hT.trace_eq_one

section StrictlyPositive

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {ι : Type*} [Fintype ι] [Nonempty ι]

open scoped InnerProductSpace

/-- **A reduced state of a faithful state is faithful** (right factor). -/
theorem _root_.IsStrictlyPositive.of_partialTraceRight_eq [CompleteSpace E]
    {T : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)} {ρ : E →L[ℂ] E}
    (hT : IsStrictlyPositive T) (b : OrthonormalBasis ι ℂ F)
    (hρ : LinearMap.partialTraceRight b T.toLinearMap = ρ.toLinearMap) :
    IsStrictlyPositive ρ := by
  refine ContinuousLinearMap.isStrictlyPositive_of_re_inner_self_pos ?_ fun x hx ↦ ?_
  · rw [ContinuousLinearMap.nonneg_iff_isPositive,
      ← ContinuousLinearMap.isPositive_toLinearMap_iff, ← hρ]
    exact LinearMap.partialTraceRight_isPositive b ((ContinuousLinearMap.isPositive_toLinearMap_iff
      T).mp ((ContinuousLinearMap.nonneg_iff_isPositive T).mp hT.nonneg))
  · rw [← ContinuousLinearMap.coe_coe ρ, ← hρ,
      LinearMap.inner_partialTraceRight_self, map_sum]
    refine Finset.sum_pos (fun k _ ↦ ?_) Finset.univ_nonempty
    have hzne : x ⊗ₜ[ℂ] b k ≠ 0 := by
      rw [← norm_ne_zero_iff, TensorProduct.norm_tmul]; simp [hx]
    rw [← RCLike.conj_re, inner_conj_symm]
    exact hT.re_inner_self_pos hzne

/-- **A reduced state of a faithful state is faithful** (left factor). -/
theorem _root_.IsStrictlyPositive.of_partialTraceLeft_eq [CompleteSpace F]
    {T : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)} {ρ : F →L[ℂ] F}
    (hT : IsStrictlyPositive T) (b : OrthonormalBasis ι ℂ E)
    (hρ : LinearMap.partialTraceLeft b T.toLinearMap = ρ.toLinearMap) :
    IsStrictlyPositive ρ := by
  refine ContinuousLinearMap.isStrictlyPositive_of_re_inner_self_pos ?_ fun y hy ↦ ?_
  · rw [ContinuousLinearMap.nonneg_iff_isPositive,
      ← ContinuousLinearMap.isPositive_toLinearMap_iff, ← hρ]
    exact LinearMap.partialTraceLeft_isPositive b ((ContinuousLinearMap.isPositive_toLinearMap_iff
      T).mp ((ContinuousLinearMap.nonneg_iff_isPositive T).mp hT.nonneg))
  · rw [← ContinuousLinearMap.coe_coe ρ, ← hρ,
      LinearMap.inner_partialTraceLeft_self, map_sum]
    refine Finset.sum_pos (fun k _ ↦ ?_) Finset.univ_nonempty
    have hzne : b k ⊗ₜ[ℂ] y ≠ 0 := by
      rw [← norm_ne_zero_iff, TensorProduct.norm_tmul]; simp [hy]
    rw [← RCLike.conj_re, inner_conj_symm]
    exact hT.re_inner_self_pos hzne

end StrictlyPositive

end ContinuousLinearMap
