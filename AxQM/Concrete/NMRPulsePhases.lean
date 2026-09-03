/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliEigenstateBloch

/-!
# Numeric bridges for the NMR `π/4`-coupling phases

Pure `ℂ`-arithmetic facts for the NMR §7.7.3 exercises: the closed forms of the coupled
free-evolution phases `e^{∓iπ/4}` on the two-spin computational branches.
-/

namespace AxQM.Concrete

open Complex (I)

/-- `e^{-iπ/4} = (1 - i)/√2`, the coupled-evolution phase on the `|00⟩`/`|11⟩` branches. -/
theorem exp_neg_pi_div_four_mul_I :
    Complex.exp (-(I * ((Real.pi : ℂ) / 4))) = invSqrt2 - invSqrt2 * I := by
  rw [show -(I * ((Real.pi : ℂ) / 4)) = ((-(Real.pi / 4) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    ofReal_cos_pi_div_four, Complex.ofReal_neg, ofReal_sin_pi_div_four]
  ring

/-- `e^{iπ/4} = (1 + i)/√2`, the coupled-evolution phase on the `|01⟩`/`|10⟩` branches. -/
theorem exp_pi_div_four_mul_I :
    Complex.exp (I * ((Real.pi : ℂ) / 4)) = invSqrt2 + invSqrt2 * I := by
  rw [show (I * ((Real.pi : ℂ) / 4)) = ((Real.pi / 4 : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ofReal_cos_pi_div_four,
    ofReal_sin_pi_div_four]

end AxQM.Concrete
