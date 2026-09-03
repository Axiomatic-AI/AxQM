/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.Complex.Circle

/-!
# Concrete: unit-modulus arithmetic for `e^{iφ}`

The unit-modulus fact for a phase, in the form `star (e^{iφ}) · e^{iφ} = 1`.
-/

namespace AxQM.Concrete

/-- The phase `e^{iφ}` has unit modulus: `conj(e^{iφ}) · e^{iφ} = 1`. -/
theorem star_exp_ofReal_mul_I_mul_self (φ : ℝ) :
    star (Complex.exp ((φ : ℂ) * Complex.I)) * Complex.exp ((φ : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    ← Complex.exp_add,
    show (φ : ℂ) * (-Complex.I) + (φ : ℂ) * Complex.I = 0 by ring, Complex.exp_zero]

end AxQM.Concrete
