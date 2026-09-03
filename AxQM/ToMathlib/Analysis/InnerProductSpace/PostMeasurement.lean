/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.Density

/-!
# The post-measurement operation

Operator algebra underlying measurement state-update (Nielsen–Chuang Eq. (8.5)).
For a family of measurement operators `M` and an operator `ρ`, the
**post-measurement operation** `Eₘ(ρ) = Mₘ ρ Mₘ†` is positive when `ρ` is; its
normalization `Eₘ(ρ)/tr(Eₘ(ρ))` is a density operator when `ρ` is and the outcome
is possible.
-/

open scoped InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [fin : FiniteDimensional ℂ H]

/-- The **post-measurement operation** of outcome `m`: `Eₘ(ρ) = Mₘ ρ Mₘ†`. -/
noncomputable def postOp (M : ι → H →L[ℂ] H) (ρ : H →L[ℂ] H) (m : ι) : H →L[ℂ] H :=
  (M m) ∘L ρ ∘L (adjoint (M m))

omit fin in
/-- `Eₘ(ρ) = Mₘ ρ Mₘ†` is positive when `ρ` is positive. -/
theorem postOp_isPositive (M : ι → H →L[ℂ] H) {ρ : H →L[ℂ] H}
    (hρ : ρ.IsPositive) (m : ι) : (postOp M ρ m).IsPositive :=
  hρ.conj_adjoint (M m)

/-- `tr(Mₘ ρ Mₘ†) = tr(Mₘ† Mₘ ρ)` (cyclicity of the trace). -/
theorem trace_postOp (M : ι → H →L[ℂ] H) (ρ : H →L[ℂ] H) (m : ι) :
    LinearMap.trace ℂ H (postOp M ρ m : H →ₗ[ℂ] H)
      = LinearMap.trace ℂ H
          (((adjoint (M m)) ∘L (M m) ∘L ρ : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  simp only [postOp, ContinuousLinearMap.coe_comp]
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.trace_comp_comm',
    LinearMap.comp_assoc]

include fin in
/-- For positive `ρ`, the trace of the post-measurement operation is a non-negative
real. -/
theorem trace_postOp_eq_ofReal_re (M : ι → H →L[ℂ] H) {ρ : H →L[ℂ] H}
    (hρ : ρ.IsPositive) (m : ι) :
    LinearMap.trace ℂ H (postOp M ρ m : H →ₗ[ℂ] H)
      = ((RCLike.re (LinearMap.trace ℂ H (postOp M ρ m : H →ₗ[ℂ] H)) : ℝ) : ℂ) := by
  have hsym := (postOp_isPositive M hρ m).toLinearMap.isSymmetric
  rw [hsym.re_trace_eq_sum_eigenvalues rfl, hsym.trace_eq_sum_eigenvalues rfl]
  push_cast
  rfl

/-- The **normalized post-measurement state** of outcome `m`:
`Eₘ(ρ)/tr(Eₘ(ρ)) = (re tr(Eₘ(ρ)))⁻¹ • Eₘ(ρ)`. -/
noncomputable def postState (M : ι → H →L[ℂ] H) (ρ : H →L[ℂ] H) (m : ι) : H →L[ℂ] H :=
  ((RCLike.re (LinearMap.trace ℂ H (postOp M ρ m : H →ₗ[ℂ] H)) : ℝ)⁻¹ : ℂ) • postOp M ρ m

include fin in
/-- When `ρ` is a density operator and outcome `m` is possible (`tr(Eₘ(ρ)) ≠ 0`),
the normalized post-measurement operator is again a density operator. -/
theorem postState_isDensityOp (M : ι → H →L[ℂ] H) {ρ : H →L[ℂ] H} (hρ : ρ.IsDensityOp)
    (m : ι)
    (hne : RCLike.re (LinearMap.trace ℂ H (postOp M ρ m : H →ₗ[ℂ] H)) ≠ 0) :
    (postState M ρ m).IsDensityOp := by
  have hEpos : (postOp M ρ m).IsPositive := postOp_isPositive M hρ.isPositive m
  have hpnn : 0 ≤ RCLike.re (LinearMap.trace ℂ H (postOp M ρ m : H →ₗ[ℂ] H)) :=
    (RCLike.nonneg_iff.mp hEpos.toLinearMap.trace_nonneg).1
  refine ⟨?_, ?_⟩
  · rw [postState]
    refine hEpos.smul_of_nonneg ?_
    rw [RCLike.le_iff_re_im]
    refine ⟨?_, ?_⟩
    · simpa using inv_nonneg.mpr hpnn
    · simp
  · rw [postState, ContinuousLinearMap.coe_smul, map_smul, smul_eq_mul]
    nth_rewrite 2 [trace_postOp_eq_ofReal_re M hρ.isPositive m]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_eq_one,
      inv_mul_cancel₀ hne]

omit fin in
/-- The post-measurement operation `Eₘ(ρ) = Mₘ ρ Mₘ†` is `ℂ`-linear in the operator argument:
`Eₘ(c ρ) = c Eₘ(ρ)`. -/
theorem postOp_smul (M : ι → H →L[ℂ] H) (c : ℂ) (ρ : H →L[ℂ] H) (m : ι) :
    postOp M (c • ρ) m = c • postOp M ρ m := by
  simp only [postOp, smul_comp, comp_smul]


end ContinuousLinearMap
