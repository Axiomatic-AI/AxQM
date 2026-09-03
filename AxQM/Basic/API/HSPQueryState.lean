/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CosetDensityState
import AxQM.Basic.PartialTrace
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.ToMathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# AxQM.Basic.API — the HSP query state (5.80)

The **single-copy query state** of Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup
problem): for a finite group `G`, a finite range `X` and a query function `f : G → X`, the `m = 1`
case of eq. (5.80).
-/

open scoped InnerProductSpace TensorProduct ComplexOrder

noncomputable section

namespace AxQM

variable {G X : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype X] [DecidableEq X]

/-- The **single-copy HSP query vector** `|ψ_f⟩ = |G|^{-1/2} ∑_{g} |g⟩|f(g)⟩` (Nielsen & Chuang
eq. 5.80, `m = 1`) as an element of the composite state space `ℂ[G] ⊗ ℂ[X]`. -/
def hspQueryVec (f : G → X) : ((groupSystem G).compose (groupSystem X)).space :=
  ∑ g : G, (((Real.sqrt (Fintype.card G))⁻¹ : ℝ) : ℂ) •
    (EuclideanSpace.single g (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single (f g) (1 : ℂ))

omit [Group G] in
/-- The elementary tensors `|g⟩|f(g)⟩` of the query state form an **orthonormal family**:
`⟪|g⟩|f(g)⟩, |g'⟩|f(g')⟩⟫ = [g = g']`. -/
theorem hspQueryFactor_orthonormal (f : G → X) :
    Orthonormal ℂ (fun g : G =>
      (EuclideanSpace.single g (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single (f g) (1 : ℂ) :
        ((groupSystem G).compose (groupSystem X)).space)) := by
  rw [orthonormal_iff_ite]
  intro g g'
  rw [TensorProduct.inner_tmul]
  erw [orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single g g',
    orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single (f g) (f g')]
  by_cases hg : g = g'
  · subst hg; simp
  · simp [hg]

/-- The **HSP query vector is a unit vector**: `‖|ψ_f⟩‖ = 1`. -/
theorem hspQueryVec_norm (f : G → X) : ‖hspQueryVec f‖ = 1 := by
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hnorm : ‖(((Real.sqrt (Fintype.card G))⁻¹ : ℝ) : ℂ)‖ ^ 2 = (Fintype.card G : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), inv_pow,
      Real.sq_sqrt hG.le]
  have hsq : ‖hspQueryVec f‖ ^ 2 = 1 := by
    have h : ‖hspQueryVec f‖ ^ 2
        = ∑ _g : G, ‖(((Real.sqrt (Fintype.card G))⁻¹ : ℝ) : ℂ)‖ ^ 2 := by
      unfold hspQueryVec
      exact (hspQueryFactor_orthonormal f).norm_sum_smul_sq _ _
    rw [h, Finset.sum_const, Finset.card_univ, hnorm, nsmul_eq_mul,
      mul_inv_cancel₀ (ne_of_gt hG)]
  nlinarith [norm_nonneg (hspQueryVec f), hsq]

/-- The **single-copy HSP query state** `|ψ_f⟩` (Nielsen & Chuang eq. 5.80, `m = 1`) as a
`PureState` of the composite system `groupSystem G ⊗ groupSystem X`. -/
def hspQueryState (f : G → X) : PureState ((groupSystem G).compose (groupSystem X)) where
  vec := hspQueryVec f
  normalized := hspQueryVec_norm f

end AxQM
