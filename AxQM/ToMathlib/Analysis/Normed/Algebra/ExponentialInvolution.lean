/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# The exponential of a scalar multiple of an involution

Let `𝔸` be a normed `ℂ`-algebra and `a : 𝔸` an element with `a * a = 1` (an *involution*,
e.g. a Pauli matrix, a reflection, or any square root of `1`). This file gives the closed form of
its complex exponential.

## Main results

* `NormedSpace.exp_smul_mul_I_of_mul_self_eq_one`: its real-angle trigonometric form
  `exp ((x * i) • a) = cos x • 1 + (sin x * i) • a` (Nielsen & Chuang, Exercise 4.2, eq. 4.7).
-/

@[expose] public section

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]

/-- **Euler's formula for an involution.** If `a` satisfies `a * a = 1` in a normed `ℂ`-algebra,
then for any `z : ℂ`, `exp (z • a) = Complex.cosh z • 1 + Complex.sinh z • a`. -/
theorem exp_smul_of_mul_self_eq_one {a : 𝔸} (ha : a * a = 1) (z : ℂ) :
    exp (z • a) = Complex.cosh z • (1 : 𝔸) + Complex.sinh z • a := by
  have ha2 : a ^ 2 = 1 := by rw [sq]; exact ha
  have hpe : ∀ k : ℕ, a ^ (2 * k) = 1 := fun k => by rw [pow_mul, ha2, one_pow]
  have hpo : ∀ k : ℕ, a ^ (2 * k + 1) = a := fun k => by rw [pow_succ, hpe k, one_mul]
  rw [exp_eq_tsum ℂ]
  refine HasSum.tsum_eq ?_
  refine HasSum.even_add_odd ?_ ?_
  · -- even terms: `(2k)!⁻¹ • (z • a) ^ (2k) = (z^(2k)/(2k)!) • 1`, summing to `cosh z • 1`
    have h : (fun k : ℕ => (↑(2 * k).factorial : ℂ)⁻¹ • (z • a) ^ (2 * k))
        = (fun k : ℕ => (z ^ (2 * k) / ↑(2 * k).factorial) • (1 : 𝔸)) := by
      funext k; rw [smul_pow, hpe k, smul_smul, div_eq_mul_inv, mul_comm]
    rw [h]; exact (Complex.hasSum_cosh z).smul_const (1 : 𝔸)
  · -- odd terms: `(2k+1)!⁻¹ • (z • a) ^ (2k+1) = (z^(2k+1)/(2k+1)!) • a`, summing to `sinh z • a`
    have h : (fun k : ℕ => (↑(2 * k + 1).factorial : ℂ)⁻¹ • (z • a) ^ (2 * k + 1))
        = (fun k : ℕ => (z ^ (2 * k + 1) / ↑(2 * k + 1).factorial) • a) := by
      funext k; rw [smul_pow, hpo k, smul_smul, div_eq_mul_inv, mul_comm]
    rw [h]; exact (Complex.hasSum_sinh z).smul_const a

/-- **Nielsen & Chuang, Exercise 4.2, equation (4.7).** For an involution `a` (`a * a = 1`) in a
normed `ℂ`-algebra and a *real* number `x`, `exp ((x * i) • a) = cos x • 1 + (sin x * i) • a`,
that is, `exp (i x a) = cos x · 1 + i sin x · a`.
-/
theorem exp_smul_mul_I_of_mul_self_eq_one {a : 𝔸} (ha : a * a = 1) (x : ℝ) :
    exp (((x : ℂ) * Complex.I) • a)
      = (Real.cos x : ℂ) • (1 : 𝔸) + ((Real.sin x : ℂ) * Complex.I) • a := by
  rw [exp_smul_of_mul_self_eq_one ha, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

end NormedSpace
