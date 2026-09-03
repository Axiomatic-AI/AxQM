/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochPureState

/-!
# Concrete: the `π/4` half-angle amplitudes of the §1.2 Bloch kets

Nielsen & Chuang, Exercise 4.1 (p. 174) asks for the Bloch-sphere points of the normalized Pauli
eigenvectors, whose equatorial (`θ = π/2`) kets carry the amplitude `cos(π/4) = sin(π/4) = 1/√2`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- `√2/2 = (√2)⁻¹` in `ℝ` (the two spellings of `1/√2`). -/
private theorem sqrt2_div_two : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [div_eq_iff (two_ne_zero), inv_mul_eq_div, eq_div_iff h2]
  exact Real.mul_self_sqrt (by norm_num)

/-- `cos(π/4) = 1/√2` (as a complex number): the `(θ = π/2)` half-angle value is the shared
`X`/`Y`-eigenvector amplitude `invSqrt2`. -/
theorem ofReal_cos_pi_div_four : ((Real.cos (Real.pi / 4) : ℝ) : ℂ) = invSqrt2 := by
  rw [Real.cos_pi_div_four, sqrt2_div_two, Complex.ofReal_inv, invSqrt2]

/-- `sin(π/4) = 1/√2` (as a complex number). -/
theorem ofReal_sin_pi_div_four : ((Real.sin (Real.pi / 4) : ℝ) : ℂ) = invSqrt2 := by
  rw [Real.sin_pi_div_four, sqrt2_div_two, Complex.ofReal_inv, invSqrt2]

end AxQM.Concrete
