/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Square roots, strict positivity and a perturbation sequence in a C⋆-algebra

## Main results

* `cfc_real_sqrt_mul_self_of_nonneg`, `cfc_real_sqrt_nonneg`: the continuous functional
  calculus square root of a nonnegative element squares back to it, and is nonnegative.
* `convex_isStrictlyPositive`: the strictly positive elements form a convex set.
* `isStrictlyPositive_add_smul_one`: adding a positive multiple of `1` to a nonnegative
  element gives a strictly positive one.
* `perturbedSeq`: the sequence `a + (n + 1)⁻¹ • 1` of strictly positive elements
  converging to a nonnegative `a`.

-/

@[expose] public section

namespace CStarAlgebra

section
open scoped NNReal CStarAlgebra
local notation "σₙ" => quasispectrum
variable {A : Type*} [CStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- **CFC `f * f = id` composition identity**: if `f` satisfies `f x * f x = x` on
`spectrum ℝ a`, then `cfc f a * cfc f a = a`. -/
theorem _root_.cfc_mul_self_eq_self_of_mul_self_eqOn_id {f : ℝ → ℝ} {a : A}
    (hf : (spectrum ℝ a).EqOn (fun x ↦ f x * f x) id)
    (hcont : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc f a * cfc f a = a := by
  rw [← cfc_mul _ _ a]
  conv_rhs => rw [← cfc_id ℝ a]
  exact cfc_congr hf

end

section
open scoped NNReal CStarAlgebra
local notation "σₙ" => quasispectrum
variable {A : Type*} [CStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

/-- **Unital-CFC sibling of `CFC.sqrt_mul_sqrt_self`**: for a positive element `a` in a
unital C*-algebra, `cfc Real.sqrt a * cfc Real.sqrt a = a`. Whereas `CFC.sqrt` is built from
the non-unital `cfcₙ NNReal.sqrt`, this lemma uses the unital `cfc Real.sqrt` form, which is
the natural spelling whenever the consumer already has `0 ≤ a`. -/
theorem _root_.cfc_real_sqrt_mul_self_of_nonneg {a : A} (ha : 0 ≤ a := by cfc_tac) :
    cfc Real.sqrt a * cfc Real.sqrt a = a :=
  cfc_mul_self_eq_self_of_mul_self_eqOn_id fun x hx ↦
    Real.mul_self_sqrt (spectrum_nonneg_of_nonneg ha hx)

end

section
open scoped NNReal CStarAlgebra
local notation "σₙ" => quasispectrum
variable {A : Type*} [CStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

/-- **CFC sqrt is always non-negative**: `0 ≤ cfc Real.sqrt a` for any `a`. Holds
unconditionally because `Real.sqrt _ ≥ 0` on all of ℝ (junk values for negative inputs are
also non-negative). -/
theorem _root_.cfc_real_sqrt_nonneg (a : A) : 0 ≤ cfc Real.sqrt a :=
  cfc_nonneg fun x _ ↦ Real.sqrt_nonneg x

end

section
open scoped NNReal CStarAlgebra
local notation "σₙ" => quasispectrum
variable {A : Type*} [CStarAlgebra A]
open CFC
variable [PartialOrder A] [StarOrderedRing A]

/-- For `0 ≤ a` in a C*-algebra and `0 < c` in the scalar field, `a + c • 1` is strictly
positive. The canonical "regularization" step for extending
strict-positivity-conditional results to general positive elements. -/
theorem _root_.isStrictlyPositive_add_smul_one {𝕜 : Type*} [Semifield 𝕜] [PartialOrder 𝕜]
    [Algebra 𝕜 A] [PosSMulMono 𝕜 A] {a : A} (ha : 0 ≤ a) {c : 𝕜} (hc : 0 < c) :
    IsStrictlyPositive (a + c • 1) := by
  refine IsStrictlyPositive.nonneg_add ha ?_
  rw [← Algebra.algebraMap_eq_smul_one]
  exact isStrictlyPositive_algebraMap hc

end

section
open scoped NNReal CStarAlgebra
local notation "σₙ" => quasispectrum
variable {A : Type*} [CStarAlgebra A]
open CFC
variable [PartialOrder A] [StarOrderedRing A]

/-- The set of strictly positive elements of a unital C⋆-algebra is convex. -/
@[grind ←]
lemma _root_.convex_isStrictlyPositive :
    Convex ℝ {a : A | IsStrictlyPositive a} := by
  grind [convex_iff_forall_pos]

end

section
open scoped NNReal CStarAlgebra
local notation "σₙ" => quasispectrum
variable {A : Type*} [CStarAlgebra A]
open CFC
variable [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- **Perturbation sequence** `n ↦ a + (1/(n+1)) • 1`. Strictly positive when `0 ≤ a`;
converges to `a` as `n → ∞`. The canonical regularization for extending
strict-positivity-conditional results to general positive elements. -/
noncomputable def _root_.perturbedSeq (a : A) (n : ℕ) : A :=
  a + (1 / ((n : ℝ) + 1)) • 1

end

section
open scoped NNReal CStarAlgebra
local notation "σₙ" => quasispectrum
variable {A : Type*} [CStarAlgebra A]
open CFC
variable [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp]
theorem _root_.perturbedSeq_apply (a : A) (n : ℕ) :
    perturbedSeq a n = a + (1 / ((n : ℝ) + 1)) • 1 := rfl

end

section
open scoped NNReal CStarAlgebra
local notation "σₙ" => quasispectrum
variable {A : Type*} [CStarAlgebra A]
open CFC
variable [PartialOrder A] [StarOrderedRing A]

/-- For `0 ≤ a`, every term in the perturbation sequence is strictly positive. -/
theorem _root_.perturbedSeq_isStrictlyPositive {a : A} (ha : 0 ≤ a) (n : ℕ) :
    IsStrictlyPositive (perturbedSeq a n) :=
  isStrictlyPositive_add_smul_one ha (by positivity)

end

section
open scoped NNReal CStarAlgebra
local notation "σₙ" => quasispectrum
variable {A : Type*} [CStarAlgebra A]
open CFC
variable [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
open Filter Topology in
/-- The perturbation sequence converges to `a` (via `1/(n+1) → 0`). -/
theorem _root_.tendsto_perturbedSeq (a : A) :
    Tendsto (perturbedSeq a) atTop (𝓝 a) := by
  apply Tendsto.congr (fun n ↦ (perturbedSeq_apply a n).symm)
  simpa using (tendsto_const_nhds (x := a) (f := atTop)).add
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul
      (tendsto_const_nhds (x := (1 : A)) (f := atTop)))

end

end CStarAlgebra
