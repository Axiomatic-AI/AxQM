/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Algebra.Order.Interval.Set.Group
public import AxQM.ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder

/-!
# Operator concavity of `x ↦ 1 - (1 + x)⁻¹`

## Main results

* `CFC.concaveOn_one_sub_one_add_inv` and its real-scalar form: `x ↦ 1 - (1 + x)⁻¹` is operator
  concave on the nonnegative cone.
* `CFC.cfc_one_sub_one_add_inv_eq`, `CFC.concaveOn_cfc_one_sub_one_add_inv`: the unital
  continuous-functional-calculus forms.

-/

@[expose] public section

section
variable {A : Type*} [NonUnitalCStarAlgebra A]
local notation "σₙ" => quasispectrum
local notation "σ" => spectrum
open Unitization NNReal CStarAlgebra
variable [PartialOrder A] [StarOrderedRing A]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- In a unital C⋆-algebra, `cfc (1 - (1 + ·)⁻¹) c = 1 - Ring.inverse (1 + c)` for `0 ≤ c`. -/
lemma CFC.cfc_one_sub_one_add_inv_eq (c : B) (hc : 0 ≤ c := by cfc_tac) :
    cfc (fun x : ℝ≥0 ↦ 1 - (1 + x)⁻¹) c = 1 - Ring.inverse (1 + c) := by
  have : IsStrictlyPositive (1 + c : B) := isStrictlyPositive_one.add_nonneg hc
  rw [cfc_tsub _ _ _ (fun x _ ↦ by simp) (hg := by fun_prop (disch := intro _ _; positivity)),
      cfc_const_one ℝ≥0 c, cfc_comp' (·⁻¹) (1 + ·) c ?_, cfc_add .., cfc_const_one ℝ≥0 c,
      cfc_id' ℝ≥0 c, ← CFC.rpow_neg_one_eq_cfc_inv, ← inverse_eq_rpow_neg_one]
  exact continuousOn_id.inv₀ (Set.forall_mem_image.mpr fun x _ ↦ by dsimp only [id]; positivity)

end

section
variable {A : Type*} [NonUnitalCStarAlgebra A]
local notation "σₙ" => quasispectrum
local notation "σ" => spectrum
open Unitization NNReal CStarAlgebra
variable [PartialOrder A] [StarOrderedRing A]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- In a unital C⋆-algebra, `cfc (1 - (1 + ·)⁻¹)` is operator concave on the nonnegative cone. -/
lemma CFC.concaveOn_cfc_one_sub_one_add_inv :
    ConcaveOn ℝ (Set.Ici (0 : B)) (cfc (fun x : ℝ≥0 ↦ 1 - (1 + x)⁻¹)) := by
  refine ⟨convex_Ici 0, fun a (ha : 0 ≤ a) b (hb : 0 ≤ b) α β hα hβ hαβ ↦ ?_⟩
  have hab : (0 : B) ≤ α • a + β • b := add_nonneg (smul_nonneg hα ha) (smul_nonneg hβ hb)
  rw [cfc_one_sub_one_add_inv_eq a ha, cfc_one_sub_one_add_inv_eq b hb,
      cfc_one_sub_one_add_inv_eq _ hab, smul_sub, smul_sub, sub_add_sub_comm,
      show α • (1 : B) + β • 1 = 1 by rw [← add_smul, hαβ, one_smul], sub_le_sub_iff_left]
  exact convexOn_ringInverse_one_add.2 ha hb hα hβ hαβ

end

section
variable {A : Type*} [NonUnitalCStarAlgebra A]
local notation "σₙ" => quasispectrum
local notation "σ" => spectrum
open Unitization NNReal CStarAlgebra
variable [PartialOrder A] [StarOrderedRing A]

/-- The function `x ↦ 1 - (1 + x)⁻¹` is operator concave on `Set.Ici (0 : A)`. -/
lemma CFC.concaveOn_one_sub_one_add_inv :
    ConcaveOn ℝ (Set.Ici (0 : A)) (cfcₙ (fun x : ℝ≥0 ↦ 1 - (1 + x)⁻¹)) := by
  refine ⟨convex_Ici 0, fun a ha b hb α β hα hβ hαβ ↦ ?_⟩
  simp only [Set.mem_Ici] at ha hb
  -- Lift the inequality to A⁺¹ via inr and use the unital helper.
  rw [← inr_le_iff ..]
  simp only [Unitization.inr_add, Unitization.inr_smul]
  rw [nnreal_cfcₙ_eq_cfc_inr a _, nnreal_cfcₙ_eq_cfc_inr b _,
      nnreal_cfcₙ_eq_cfc_inr (α • a + β • b) _, Unitization.inr_add,
      Unitization.inr_smul, Unitization.inr_smul]
  rw [← inr_nonneg_iff] at ha hb
  exact CFC.concaveOn_cfc_one_sub_one_add_inv.2 ha hb hα hβ hαβ

end

section
variable {A : Type*} [NonUnitalCStarAlgebra A]
local notation "σₙ" => quasispectrum
local notation "σ" => spectrum
open Unitization NNReal CStarAlgebra
variable [PartialOrder A] [StarOrderedRing A]

/-- The function `x ↦ 1 - (1 + x)⁻¹` (real version) is operator concave on `Set.Ici (0 : A)`. -/
lemma CFC.concaveOn_one_sub_one_add_inv_real :
    ConcaveOn ℝ (Set.Ici (0 : A)) (cfcₙ (fun x : ℝ ↦ 1 - (1 + x)⁻¹)) := by
  refine CFC.concaveOn_one_sub_one_add_inv.congr fun a (ha : 0 ≤ a) ↦ ?_
  rw [cfcₙ_nnreal_eq_real _ _ ha]
  refine cfcₙ_congr fun x hx ↦ ?_
  simp [show 0 ≤ x by grind]

end
