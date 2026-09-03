/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import AxQM.ToMathlib.Analysis.CStarAlgebra.ApproximateUnit

/-!
# The integral representation of `x ^ p` for `p ∈ (1, 2)`

## Main results

* `Real.rpowIntegrand₁₂` and its API: the integrand whose improper integral over `Ioi 0`
  represents `x ^ p` for `p ∈ (1, 2)`.
* `Real.exists_measure_rpow_eq_integral_Ioo_one_two`: the scalar integral representation.
* `CFC.convexOn_cfcₙ_rpowIntegrand₁₂`: the integrand is operator convex on the nonnegative
  cone, via the continuous functional calculus.

-/

@[expose] public section

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

lemma rpowIntegrand₀₁_def : rpowIntegrand₀₁ p t x = t ^ p * (t⁻¹ - (t + x)⁻¹) := rfl

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

lemma rpowIntegrand₀₁_one_eq (p : ℝ) :
    (rpowIntegrand₀₁ p 1 : ℝ → ℝ) = fun x ↦ 1 - (1 + x)⁻¹ := by
  funext x; simp [rpowIntegrand₀₁_def]

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

/-- Integrand for representing `x ↦ x ^ p` for `p ∈ (1, 2)`. The closed form
`t ^ (p - 2) * x ^ 2 / (t + x)` is operator-convex in `x` on `Ici 0` for fixed `t ∈ Ioi 0`. -/
noncomputable def rpowIntegrand₁₂ (p t x : ℝ) : ℝ := t ^ (p - 2) * x ^ 2 / (t + x)

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

lemma rpowIntegrand₁₂_def : rpowIntegrand₁₂ p t x = t ^ (p - 2) * x ^ 2 / (t + x) := rfl

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

private lemma sub_one_mem_Ioo_zero_one_of_mem_Ioo_one_two
    (hp : p ∈ Ioo (1 : ℝ) 2) : p - 1 ∈ Ioo 0 1 := by
  push _ ∈ _ at hp; constructor <;> linarith

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

/-- The `(1, 2)` integrand factors as `x` times the `(0, 1)` integrand at shifted exponent. -/
lemma rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ (hp : p ∈ Ioo 1 2) (ht : 0 < t) (hx : 0 ≤ x) :
    rpowIntegrand₁₂ p t x = x * rpowIntegrand₀₁ (p - 1) t x := by
  rw [rpowIntegrand₁₂_def,
    rpowIntegrand₀₁_eq_pow_div (sub_one_mem_Ioo_zero_one_of_mem_Ioo_one_two hp) ht.le hx,
    show (p - 1 : ℝ) - 1 = p - 2 from by ring, sq]
  field_simp

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

@[simp]
lemma rpowIntegrand₁₂_zero_right : rpowIntegrand₁₂ p t 0 = 0 := by simp [rpowIntegrand₁₂_def]

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

/-- The `(1, 2)` integrand at `t = 1`: `rpowIntegrand₁₂ p 1 x = x^2 / (1 + x)`, independent
of `p`. -/
lemma rpowIntegrand₁₂_one_eq (p : ℝ) :
    (rpowIntegrand₁₂ p 1 : ℝ → ℝ) = fun x ↦ x ^ 2 / (1 + x) := by
  funext x; simp [rpowIntegrand₁₂_def]

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

/-- The `t`-rescaling identity: `rpowIntegrand₁₂ p t x = t ^ (p - 1) · rpowIntegrand₁₂ p 1 (x/t)`
on `Ici 0` for `t > 0`. -/
lemma rpowIntegrand₁₂_eqOn_mul_rpowIntegrand₁₂_one (ht : 0 < t) :
    (Ici 0).EqOn (rpowIntegrand₁₂ p t)
      (fun x ↦ t ^ (p - 1) * (rpowIntegrand₁₂ p 1 (t⁻¹ • x))) := by
  intro x (hx : 0 ≤ x)
  have htx : (t + x) ≠ 0 := by positivity
  have h_decomp : t ^ (p - 2) = t ^ (p - 1) * t⁻¹ := by
    rw [← Real.rpow_neg_one t, ← Real.rpow_add ht]
    congr 1; ring
  simp only [rpowIntegrand₁₂_def, smul_eq_mul, Real.one_rpow]
  rw [h_decomp]
  field_simp

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

lemma continuousOn_rpowIntegrand₁₂ (hx : 0 ≤ x) :
    ContinuousOn (rpowIntegrand₁₂ p · x) (Ioi 0) := by
  simp only [rpowIntegrand₁₂_def]
  refine ContinuousOn.div₀ ?_ (by fun_prop) (fun t (ht : 0 < t) ↦ ?_)
  · have h_pow : ContinuousOn (fun t : ℝ ↦ t ^ (p - 2)) (Ioi 0) :=
      ContinuousOn.rpow_const (f := id) (by fun_prop) (fun t ht ↦ .inl ht.ne')
    exact h_pow.mul continuousOn_const
  · positivity

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

lemma rpowIntegrand₁₂_monotoneOn (hp : p ∈ Ioo 1 2) (ht : 0 ≤ t) :
    MonotoneOn (rpowIntegrand₁₂ p t) (Ici 0) := by
  rcases ht.eq_or_lt with rfl | ht_pos
  · -- `t = 0`: integrand is identically `0` since `0 ^ (p − 2) = 0` for `p ∈ Ioo 1 2`.
    intro x _ y _ _
    simp [rpowIntegrand₁₂_def, Real.zero_rpow (by linarith [hp.2] : (p - 2 : ℝ) ≠ 0)]
  · have hp' := sub_one_mem_Ioo_zero_one_of_mem_Ioo_one_two hp
    intro x hx y hy hxy
    rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hp ht_pos hx,
        rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hp ht_pos hy]
    exact mul_le_mul hxy (rpowIntegrand₀₁_monotoneOn hp' ht_pos.le hx hy hxy)
      (rpowIntegrand₀₁_nonneg hp'.1 ht_pos.le hx) ((mem_Ici.mp hx).trans hxy)

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

lemma continuousOn_rpowIntegrand₁₂_uncurry (hp : p ∈ Ioo 1 2) (s : Set ℝ) (hs : s ⊆ Ici 0) :
    ContinuousOn (rpowIntegrand₁₂ p).uncurry (Ioi 0 ×ˢ s) := by
  refine ContinuousOn.congr
    (f := fun q : ℝ × ℝ ↦ q.2 * (rpowIntegrand₀₁ (p - 1)).uncurry q)
    (continuous_snd.continuousOn.mul (continuousOn_rpowIntegrand₀₁_uncurry
      (sub_one_mem_Ioo_zero_one_of_mem_Ioo_one_two hp) s hs)) ?_
  intro q hq
  exact rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hp hq.1 (hs hq.2)

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

lemma continuousOn_rpowIntegrand₁₂_Ici (hp : p ∈ Ioo 1 2) (ht : 0 < t) :
    ContinuousOn (rpowIntegrand₁₂ p t) (Ici 0) :=
  (continuousOn_rpowIntegrand₁₂_uncurry hp _ fun _ a ↦ a).uncurry_left _ ht

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

lemma integrableOn_rpowIntegrand₁₂_Ioi (hp : p ∈ Ioo 1 2) (hx : 0 ≤ x) :
    IntegrableOn (rpowIntegrand₁₂ p · x) (Ioi 0) := by
  refine IntegrableOn.congr_fun
    ((integrableOn_rpowIntegrand₀₁_Ioi
      (sub_one_mem_Ioo_zero_one_of_mem_Ioo_one_two hp) hx).const_mul x) ?_ measurableSet_Ioi
  intro t ht
  exact (rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hp ht hx).symm

end
end Real

namespace Real
section
open MeasureTheory Set Filter
open scoped NNReal Topology
variable {p t x : ℝ}

/-- The integral representation of the function `x ↦ x ^ p` for `p ∈ (1, 2)`. -/
lemma exists_measure_rpow_eq_integral_Ioo_one_two (hp : p ∈ Ioo 1 2) :
    ∃ μ : Measure ℝ, ∀ x ∈ Ici 0,
      (IntegrableOn (fun t ↦ rpowIntegrand₁₂ p t x) (Ioi 0) μ)
      ∧ x ^ p = ∫ t in Ioi 0, rpowIntegrand₁₂ p t x ∂μ := by
  have hp' := sub_one_mem_Ioo_zero_one_of_mem_Ioo_one_two hp
  obtain ⟨μ, hμ⟩ := exists_measure_rpow_eq_integral hp'
  refine ⟨μ, fun x (hx : 0 ≤ x) ↦ ⟨?_, ?_⟩⟩
  · refine IntegrableOn.congr_fun ((hμ x hx).1.const_mul x) ?_ measurableSet_Ioi
    intro t ht
    exact (rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hp ht hx).symm
  · have hrpow : x ^ p = x * x ^ (p - 1) := by
      nth_rw 2 [← Real.rpow_one (x := x)]
      rw [← Real.rpow_add_of_nonneg hx zero_le_one hp'.1.le]
      congr 1; ring
    rw [hrpow, (hμ x hx).2, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ ?_)
    exact (rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hp ht hx).symm

end
end Real

namespace CFC
section
open MeasureTheory Set Filter
open scoped NNReal Topology
open Real
variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A] [SMulCommClass ℝ A A]
  [IsScalarTower ℝ A A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- Generic `cfcₙ`-rescaling: if `f` is pointwise equal to `c • g ∘ (t⁻¹ • ·)` on `Ici 0`,
`g` is continuous on `Ici 0` and vanishes at `0`, then `cfcₙ f a = c • cfcₙ g (t⁻¹ • a)` for
`0 ≤ a` and `0 < t`. -/
private lemma cfcₙ_eq_smul_cfcₙ_smul_inv_of_eqOn
    {f g : ℝ → ℝ} {t c : ℝ} (ht : 0 < t)
    (h_eqOn : (Ici 0).EqOn f (fun x ↦ c * g (t⁻¹ • x)))
    (h_cont : ContinuousOn g (Ici 0)) (hg0 : g 0 = 0)
    (a : A) (ha : 0 ≤ a) :
    cfcₙ f a = c • cfcₙ g (t⁻¹ • a) := by
  have hspec : quasispectrum ℝ a ⊆ Ici 0 := by grind
  have h_mapsTo : MapsTo (t⁻¹ • · : ℝ → ℝ) (Ici 0) (Ici 0) := by
    intro x hx
    simp only [mem_Ici, smul_eq_mul] at hx ⊢
    positivity
  have h_cont_comp : ContinuousOn (fun x ↦ g (t⁻¹ • x)) (Ici 0) :=
    h_cont.comp (by fun_prop) h_mapsTo
  calc _ = cfcₙ (fun x ↦ c * (g (t⁻¹ • x))) a := cfcₙ_congr (Set.EqOn.mono hspec h_eqOn)
    _ = c • cfcₙ (fun x ↦ g (t⁻¹ • x)) a := by
          refine cfcₙ_smul (R := ℝ) c _ a (h_cont_comp.mono hspec) ?_
          simpa using hg0
    _ = c • cfcₙ g (t⁻¹ • a) := by
          congr! 1
          refine cfcₙ_comp_smul (R := ℝ) t⁻¹ g a
            (h_cont.mono (h_mapsTo.mono_left hspec).image_subset) ?_
          simpa using hg0

end
end CFC

namespace CFC
section
open MeasureTheory Set Filter
open scoped NNReal Topology
open Real
variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A] [SMulCommClass ℝ A A]
  [IsScalarTower ℝ A A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma cfcₙ_rpowIntegrand₁₂_eq_cfcₙ_rpowIntegrand₁₂_one {p t : ℝ} (hp : p ∈ Ioo 1 2) (ht : 0 < t)
    (a : A) (ha : 0 ≤ a) :
    cfcₙ (rpowIntegrand₁₂ p t) a = t ^ (p - 1) • cfcₙ (rpowIntegrand₁₂ p 1) (t⁻¹ • a) :=
  cfcₙ_eq_smul_cfcₙ_smul_inv_of_eqOn ht (rpowIntegrand₁₂_eqOn_mul_rpowIntegrand₁₂_one ht)
    (continuousOn_rpowIntegrand₁₂_Ici hp zero_lt_one) rpowIntegrand₁₂_zero_right a ha

end
end CFC

namespace CFC
section
open MeasureTheory Set Filter
open scoped NNReal Topology
open Real
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The `cfcₙ`-level decomposition at `t = 1`: `cfcₙ (rpowIntegrand₁₂ p 1) c = c - cfcₙ φ c`
where `φ x = 1 - (1 + x)⁻¹`. -/
private lemma cfcₙ_rpowIntegrand₁₂_one_eq_sub (p : ℝ) (c : A) (hc : 0 ≤ c) :
    cfcₙ (rpowIntegrand₁₂ p 1) c = c - cfcₙ (fun x : ℝ ↦ 1 - (1 + x)⁻¹) c :=
  calc cfcₙ (rpowIntegrand₁₂ p 1) c
      = cfcₙ (fun x : ℝ ↦ x - (1 - (1 + x)⁻¹)) c := by
        rw [rpowIntegrand₁₂_one_eq]
        refine cfcₙ_congr fun x hx ↦ ?_
        have : (0 : ℝ) ≤ x := by grind
        have : (1 + x : ℝ) ≠ 0 := by positivity
        field_simp; ring
    _ = cfcₙ (fun x : ℝ ↦ x) c - cfcₙ (fun x : ℝ ↦ 1 - (1 + x)⁻¹) c := by
        refine cfcₙ_sub _ _ c (hg := ?_)
        refine ContinuousOn.sub continuousOn_const (ContinuousOn.inv₀ (by fun_prop) fun x hx ↦ ?_)
        have : (0 : ℝ) ≤ x := by grind
        linarith
    _ = c - cfcₙ (fun x : ℝ ↦ 1 - (1 + x)⁻¹) c := by rw [cfcₙ_id' ℝ c]

end
end CFC

namespace CFC
section
open MeasureTheory Set Filter
open scoped NNReal Topology
open Real
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `rpowIntegrand₁₂ p t` is operator convex for all `p ∈ Ioo 1 2` and all `t ∈ Ioi 0`. -/
lemma convexOn_cfcₙ_rpowIntegrand₁₂ {p : ℝ} {t : ℝ} (hp : p ∈ Ioo 1 2) (ht : 0 < t) :
    ConvexOn ℝ (Ici (0 : A)) (cfcₙ (rpowIntegrand₁₂ p t)) := by
  refine ⟨convex_Ici 0, fun a (ha : 0 ≤ a) b (hb : 0 ≤ b) α β hα hβ hαβ ↦ ?_⟩
  have hab : (0 : A) ≤ α • a + β • b := add_nonneg (smul_nonneg hα ha) (smul_nonneg hβ hb)
  rw [cfcₙ_rpowIntegrand₁₂_eq_cfcₙ_rpowIntegrand₁₂_one hp ht a ha,
      cfcₙ_rpowIntegrand₁₂_eq_cfcₙ_rpowIntegrand₁₂_one hp ht b hb,
      cfcₙ_rpowIntegrand₁₂_eq_cfcₙ_rpowIntegrand₁₂_one hp ht (α • a + β • b) hab,
      smul_comm α (t ^ (p - 1)), smul_comm β (t ^ (p - 1)), ← smul_add]
  refine smul_le_smul_of_nonneg_left ?_ (by positivity)
  rw [cfcₙ_rpowIntegrand₁₂_one_eq_sub p _ (by positivity),
      cfcₙ_rpowIntegrand₁₂_one_eq_sub p _ (by positivity : (0 : A) ≤ t⁻¹ • a),
      cfcₙ_rpowIntegrand₁₂_one_eq_sub p _ (by positivity : (0 : A) ≤ t⁻¹ • b),
      smul_sub, smul_sub, sub_add_sub_comm,
      smul_add, smul_comm t⁻¹ α a, smul_comm t⁻¹ β b, sub_le_sub_iff_left]
  refine CFC.concaveOn_one_sub_one_add_inv_real.2
    (?_ : 0 ≤ t⁻¹ • a) (?_ : 0 ≤ t⁻¹ • b) hα hβ hαβ <;> positivity

end
end CFC
