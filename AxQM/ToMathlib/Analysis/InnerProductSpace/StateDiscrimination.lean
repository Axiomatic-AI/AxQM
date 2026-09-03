/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
public import AxQM.ToMathlib.Analysis.InnerProductSpace.LinearMap

/-!
# A POVM that distinguishes linearly independent states with certainty

Given a finite family `v : ι → E` of **linearly independent** vectors in a finite-dimensional
inner product space, this file constructs a POVM `POVM.distinguishing 𝕜 v` on the outcome set
`Option ι` — one "informative" outcome `some i` per state, plus one "inconclusive" outcome
`none` — for the *unambiguous discrimination* of the family (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 2.64).

## Main definitions

* `POVM.detector` — the detector vector for outcome `i`.
* `POVM.distinguishing` — the discriminating POVM on `Option ι`.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information* (10th
anniv. ed.). Cambridge University Press. §2.2.6, Exercise 2.64.
-/

@[expose] public section

open Module InnerProductSpace ContinuousLinearMap

noncomputable section

namespace POVM

variable {ι : Type*} [Fintype ι]
  (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The **detector vector** for outcome `i` in the family `v`: the orthogonal projection of `v i`
onto the orthogonal complement of the span of the other members `{v j | j ≠ i}`. -/
def detector (v : ι → E) (i : ι) : E :=
  (Submodule.span 𝕜 (v '' {j | j ≠ i}))ᗮ.starProjection (v i)

/-- The scale factor `c = (1 + ∑ⱼ ‖detector 𝕜 v j‖²)⁻¹` of the informative effects, chosen so
that `∑ᵢ Eᵢ ≤ 1`. -/
def distinguishingScale (v : ι → E) : ℝ := (1 + ∑ j, ‖detector 𝕜 v j‖ ^ 2)⁻¹

theorem distinguishingScale_pos (v : ι → E) : 0 < distinguishingScale 𝕜 v := by
  rw [distinguishingScale]; positivity

/-- The **informative effect** for outcome `i`. -/
def distinguishingEffect (v : ι → E) (i : ι) : E →L[𝕜] E :=
  (distinguishingScale 𝕜 v : 𝕜) • rankOne 𝕜 (detector 𝕜 v i) (detector 𝕜 v i)

theorem distinguishingEffect_isPositive (v : ι → E) (i : ι) :
    (distinguishingEffect 𝕜 v i).IsPositive :=
  (isPositive_rankOne_self (detector 𝕜 v i)).smul_of_nonneg
    (RCLike.ofReal_nonneg.mpr (distinguishingScale_pos 𝕜 v).le)

/-- The **inconclusive effect** `1 - ∑ᵢ Eᵢ` is a positive operator. -/
theorem distinguishing_isPositive_none (v : ι → E) :
    ((1 : E →L[𝕜] E) - ∑ i, distinguishingEffect 𝕜 v i).IsPositive := by
  have hcpos : 0 < distinguishingScale 𝕜 v := distinguishingScale_pos 𝕜 v
  refine isPositive_def.mpr ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.coe_sub]
    exact isPositive_one.isSymmetric.sub
      (isPositive_sum _ fun i _ => distinguishingEffect_isPositive 𝕜 v i).isSymmetric
  · intro x
    have hkey : ((1 : E →L[𝕜] E) - ∑ i, distinguishingEffect 𝕜 v i).reApplyInnerSelf x
        = ‖x‖ ^ 2 - ∑ i, distinguishingScale 𝕜 v * ‖inner 𝕜 (detector 𝕜 v i) x‖ ^ 2 := by
      rw [reApplyInnerSelf_apply, ContinuousLinearMap.sub_apply, inner_sub_left, map_sub,
        ContinuousLinearMap.one_apply, inner_self_eq_norm_sq]
      congr 1
      rw [← reApplyInnerSelf_apply, reApplyInnerSelf_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [distinguishingEffect, reApplyInnerSelf_ofReal_smul, reApplyInnerSelf_rankOne_self]
    rw [hkey, sub_nonneg]
    calc ∑ i, distinguishingScale 𝕜 v * ‖inner 𝕜 (detector 𝕜 v i) x‖ ^ 2
        ≤ ∑ i, distinguishingScale 𝕜 v * (‖detector 𝕜 v i‖ ^ 2 * ‖x‖ ^ 2) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ hcpos.le
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
      _ = distinguishingScale 𝕜 v * (∑ j, ‖detector 𝕜 v j‖ ^ 2) * ‖x‖ ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
      _ ≤ 1 * ‖x‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [distinguishingScale, inv_mul_le_iff₀ (by positivity)]
          nlinarith [Finset.sum_nonneg
            (fun j (_ : j ∈ Finset.univ) => sq_nonneg ‖detector 𝕜 v j‖)]
      _ = ‖x‖ ^ 2 := one_mul _

/-- **The discriminating POVM** for a family `v` of states.
The outcome set is `Option ι`: outcome `some i` has effect `Eᵢ = c • |detector 𝕜 v i⟩⟨…|`
(the "state `i` detected" effect), and the single outcome `none` has the inconclusive effect
`1 - ∑ᵢ Eᵢ`. -/
def distinguishing (v : ι → E) : POVM (Option ι) 𝕜 E where
  elements o := o.elim (1 - ∑ i, distinguishingEffect 𝕜 v i) (distinguishingEffect 𝕜 v)
  isPositive o := by
    cases o with
    | none => exact distinguishing_isPositive_none 𝕜 v
    | some i => exact distinguishingEffect_isPositive 𝕜 v i
  sum_eq_one := by
    rw [Fintype.sum_option]
    change (1 - ∑ i, distinguishingEffect 𝕜 v i) + ∑ i, distinguishingEffect 𝕜 v i = 1
    rw [sub_add_cancel]

end POVM
