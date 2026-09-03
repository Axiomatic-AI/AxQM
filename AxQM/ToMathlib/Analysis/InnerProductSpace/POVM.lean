/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.Density
public import AxQM.ToMathlib.Analysis.InnerProductSpace.TraceNorm
public import AxQM.ToMathlib.Analysis.RCLike.Basic
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Trace

/-!
# Positive operator-valued measures (POVMs)

A **POVM** on a finite-dimensional inner product space `E` over `𝕜` (`ℝ` or `ℂ`) with
finite outcome index `ι` is a family of positive operators `M.elements i : E →L[𝕜] E`
indexed by `i : ι`, satisfying `∑ i, M.elements i = 1`. POVMs generalize projective
measurements: each `M.elements i` is a "soft" positive operator with the closure-to-
identity replacing idempotence.

## Main definitions

- `POVM ι 𝕜 E`: a POVM on `E` over `𝕜` with outcome index `ι`.

## Main results

- `POVM.isPositive`, `POVM.sum_eq_one`: unpacking lemmas.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information*
(10th anniv. ed.). Cambridge University Press. §2.2.6.
-/

@[expose] public section

/-- A **positive operator-valued measure (POVM)** on a finite-dim inner product space
`E` over `𝕜` with finite outcome index `ι`: a family of positive operators summing to
the identity. -/
@[ext]
structure POVM (ι : Type*) [Fintype ι] (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  /-- The operator-valued measure. -/
  elements : ι → E →L[𝕜] E
  /-- Each element is positive. -/
  isPositive : ∀ i, (elements i).IsPositive
  /-- The elements sum to the identity. -/
  sum_eq_one : ∑ i, elements i = 1

namespace POVM

variable {ι : Type*} [Fintype ι]
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Born rule**: the probability of measurement outcome `i` for state `ρ` under POVM
`M`, defined as `Re tr(M.elements i ∘L ρ)`. -/
noncomputable def toPMF [FiniteDimensional 𝕜 E]
    (M : POVM ι 𝕜 E) (ρ : E →L[𝕜] E) (i : ι) : ℝ :=
  RCLike.re (LinearMap.trace 𝕜 E ((M.elements i ∘L ρ : E →L[𝕜] E) : E →ₗ[𝕜] E))

theorem toPMF_eq [FiniteDimensional 𝕜 E]
    (M : POVM ι 𝕜 E) (ρ : E →L[𝕜] E) (i : ι) :
    M.toPMF ρ i =
      RCLike.re (LinearMap.trace 𝕜 E ((M.elements i ∘L ρ : E →L[𝕜] E) : E →ₗ[𝕜] E)) :=
  rfl

variable [FiniteDimensional 𝕜 E]

/-- **Non-negativity** of measurement probabilities: for a positive operator `ρ` (in particular, a
density operator), each outcome probability is non-negative. -/
theorem toPMF_nonneg (M : POVM ι 𝕜 E) {ρ : E →L[𝕜] E}
    (hρ : ρ.IsPositive) (i : ι) :
    0 ≤ M.toPMF ρ i := by
  rw [toPMF_eq, ContinuousLinearMap.coe_comp,
    hρ.toLinearMap.isSymmetric.trace_comp_eq_sum_eigenvalues_inner rfl _, RCLike.re_sum]
  refine Finset.sum_nonneg fun j _ ↦ ?_
  rw [RCLike.re_ofReal_mul]
  refine mul_nonneg (hρ.toLinearMap.nonneg_eigenvalues rfl j) ?_
  rw [← (M.isPositive i).toLinearMap.isSymmetric (_ : E) (_ : E)]
  exact (M.isPositive i).toLinearMap.re_inner_nonneg_left _

omit [FiniteDimensional 𝕜 E] in
/-- For a POVM `M` and any operator `T`, summing the traces of `(M.elements i) ∘L T`
over outcomes recovers the trace of `T`. -/
theorem sum_trace_elements_comp (M : POVM ι 𝕜 E) (T : E →L[𝕜] E) :
    ∑ i, LinearMap.trace 𝕜 E ((M.elements i ∘L T : E →L[𝕜] E) : E →ₗ[𝕜] E) =
      LinearMap.trace 𝕜 E T.toLinearMap := by
  rw [← map_sum (LinearMap.trace 𝕜 E) _ Finset.univ,
    ← ContinuousLinearMap.coe_sum,
    ← ContinuousLinearMap.finset_sum_comp _ _, M.sum_eq_one,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_one,
    Module.End.one_eq_id, LinearMap.id_comp]

/-- **Sums-to-one**: for a density operator `ρ`, the outcome probabilities form a probability
distribution. -/
theorem sum_toPMF_eq_one (M : POVM ι 𝕜 E) {ρ : E →L[𝕜] E} (hρ : ρ.IsDensityOp) :
    ∑ i, M.toPMF ρ i = 1 := by
  simp_rw [toPMF_eq]
  rw [← RCLike.re_sum, M.sum_trace_elements_comp, hρ.trace_eq_one, RCLike.one_re]

end POVM
