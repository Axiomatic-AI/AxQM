/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import AxQM.ToMathlib.Analysis.Normed.Algebra.ExponentialInvolution

/-!
# Concrete: the exponential of `i θ (n · σ)` (Nielsen & Chuang, Exercise 2.35)

For a real *unit* three-vector `n` and a real angle `θ`, the exponential of `i θ (n · σ)` has the
closed form `cos θ • I + i sin θ • (n · σ)`.

## Main results

* `pauliDot_exp_of_unit`: `exp (i θ (n · σ)) = cos θ • I + i sin θ • (n · σ)` for a unit vector `n`.
-/

namespace AxQM.Concrete

open NormedSpace

/-- **Nielsen & Chuang, Exercise 2.35** (exponential of the Pauli matrices). For a real unit vector
`n` (`n₀² + n₁² + n₂² = 1`) and a real angle `θ`,
`exp (i θ (n · σ)) = cos θ • I + i sin θ • (n · σ)`,
where `n · σ = pauliDot n`.

The exponent `i θ (n · σ)` is written as `(θ * i) • pauliDot n`. -/
theorem pauliDot_exp_of_unit {n : Fin 3 → ℝ}
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (θ : ℝ) :
    exp (((θ : ℂ) * Complex.I) • pauliDot n)
      = (Real.cos θ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + ((Real.sin θ : ℂ) * Complex.I) • pauliDot n := by
  open scoped Matrix.Norms.Operator in
  exact exp_smul_mul_I_of_mul_self_eq_one (pauliDot_mul_self_of_unit hn) θ

end AxQM.Concrete
