/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.UniformSuperposition
import AxQM.Basic.API.QuditMeasurement

/-!
# AxQM.Basic.API — the uniform superposition over a subset (the solution state `|β⟩`)

The **uniform superposition over a subset** `T` of the computational basis of `qudit d`.

## Main declarations
* `subsetUniformSuperposition T hT` — the pure state `|β⟩ = M⁻¹ᐟ² ∑_{x∈T} |x⟩`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- The **uniform superposition over a subset** `T` of the computational basis of `qudit d`. It is
normalised because the `|x⟩` (`x ∈ T`) are orthonormal, so `‖∑_{x∈T} |x⟩‖ = √M`, and the
prefactor `M⁻¹ᐟ²` cancels it. For Exercise 6.11, `T` is the set of `M` search solutions and
`|β⟩` the state the search evolution rotates `|ψ⟩` onto. -/
def subsetUniformSuperposition (T : Finset (Fin d)) (hT : T.Nonempty) : PureState (qudit d) where
  vec := (Real.sqrt T.card : ℂ)⁻¹ • ∑ x ∈ T, (quditBasis x).vec
  normalized := by
    have hM : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
    change ‖(Real.sqrt T.card : ℂ)⁻¹ • ∑ x ∈ T, EuclideanSpace.single x (1 : ℂ)‖ = 1
    rw [norm_smul]
    have h1 : ‖(Real.sqrt T.card : ℂ)⁻¹‖ = (Real.sqrt T.card)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hcoord : ∀ y : Fin d, (∑ x ∈ T, EuclideanSpace.single x (1 : ℂ)).ofLp y
        = if y ∈ T then 1 else 0 := by
      intro y
      rw [WithLp.ofLp_sum, Finset.sum_apply]
      simp [PiLp.single_apply, Finset.sum_ite_eq]
    have h2 : ‖∑ x ∈ T, EuclideanSpace.single x (1 : ℂ)‖ = Real.sqrt T.card := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      have hnorm : ∀ y : Fin d, ‖(∑ x ∈ T, EuclideanSpace.single x (1 : ℂ)).ofLp y‖ ^ 2
          = if y ∈ T then (1 : ℝ) else 0 := by
        intro y; rw [hcoord]; split <;> simp
      rw [Finset.sum_congr rfl (fun y _ => hnorm y), Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h1, h2, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hM)]

end AxQM
