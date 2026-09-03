/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliEigenvectors
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.VecNotation

/-!
# Concrete data for the tetrahedral (SIC) qubit ensemble

This file collects the concrete data behind Nielsen & Chuang's Exercise 12.4: the four amplitude
vectors of the tetrahedral (SIC) qubit ensemble.

## Main results

* `sicKet` — the four concrete amplitude vectors in `Fin 2 → ℂ`.
* `sicKet_normSq` — each is a unit vector: `‖(sicKet k) 0‖² + ‖(sicKet k) 1‖² = 1`.
-/

open Complex Matrix

namespace AxQM.Concrete

/-- The primitive cube root of unity `ω = e^{2πi/3}` used in the SIC amplitudes. -/
noncomputable def sicOmega : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / 3)

/-- The cube root of unity `ω = e^{2πi/3}` lies on the unit circle: `‖ω‖ = 1`. -/
lemma sicOmega_norm : ‖sicOmega‖ = 1 := by
  rw [sicOmega, show (2 * ↑Real.pi * Complex.I / 3) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The four SIC amplitude vectors `|X₁⟩, …, |X₄⟩` of Exercise 12.4, as vectors in `Fin 2 → ℂ`:
`|X₁⟩ = (1, 0)` and `|Xₖ₊₁⟩ = (√(1/3), √(2/3)·ωᵏ)` for `k = 0, 1, 2` with `ω = e^{2πi/3}`. -/
noncomputable def sicKet : Fin 4 → (Fin 2 → ℂ)
  | 0 => ![1, 0]
  | 1 => ![(Real.sqrt 3 : ℂ)⁻¹, (Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹]
  | 2 => ![(Real.sqrt 3 : ℂ)⁻¹, (Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * sicOmega]
  | 3 => ![(Real.sqrt 3 : ℂ)⁻¹, (Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * sicOmega ^ 2]

/-- Each SIC amplitude vector is a unit vector: `‖(sicKet k) 0‖² + ‖(sicKet k) 1‖² = 1`. -/
lemma sicKet_normSq (k : Fin 4) : ‖sicKet k 0‖ ^ 2 + ‖sicKet k 1‖ ^ 2 = 1 := by
  have h3 : ‖(Real.sqrt 3 : ℂ)⁻¹‖ ^ 2 = 1 / 3 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 3), inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  have hβ : ‖(Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹‖ ^ 2 = 2 / 3 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), h3]; norm_num
  have hβω : ‖(Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * sicOmega‖ ^ 2 = 2 / 3 := by
    rw [norm_mul, mul_pow, sicOmega_norm, one_pow, mul_one, hβ]
  have hβω2 : ‖(Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * sicOmega ^ 2‖ ^ 2 = 2 / 3 := by
    rw [norm_mul, mul_pow, norm_pow, sicOmega_norm, one_pow, one_pow, mul_one, hβ]
  fin_cases k <;>
    simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp
  · rw [h3, hβ]; norm_num
  · rw [h3, hβω]; norm_num
  · rw [h3, hβω2]; norm_num

end AxQM.Concrete
