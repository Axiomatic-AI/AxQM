/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The finite discrete Fourier transform of a periodic function

For a function `f : ℤ → ℂ` that is periodic with period `r` and a length `N` that is an integer
multiple of `r`, this file computes the normalized length-`N` discrete Fourier transform
`f̂(ℓ) = (1/√N) ∑_{x=0}^{N-1} exp(-2πi ℓ x / N) f(x)` and shows it is supported on the multiples
of `N / r`, where its value is `√(N/r)` times the length-`r` transform of the same function.

## Main definitions

* `normDFT` : the normalized finite discrete Fourier transform
  `normDFT n f ℓ = (√n)⁻¹ ∑_{x<n} exp(-2πi ℓ x / n) f x`.

## Main statements

* `normDFT_periodic_eq_zero` : if `ℓ` is **not** a multiple of `N / r`, then `normDFT N f ℓ = 0`.
* `normDFT_periodic_mul` : `normDFT N f (k · (N/r)) = √(N/r) · normDFT r f k`.
-/

open Finset Complex
open scoped Real

@[expose] public section

variable {f : ℤ → ℂ}

/-- The normalized finite discrete Fourier transform of `f : ℤ → ℂ` at length `n`, following
Nielsen & Chuang eq. (5.68)/(5.63): `normDFT n f ℓ = (1/√n) ∑_{x<n} exp(-2πi ℓ x / n) f x`. -/
noncomputable def normDFT (n : ℕ) (f : ℤ → ℂ) (ℓ : ℤ) : ℂ :=
  (Real.sqrt (n : ℝ) : ℂ)⁻¹ *
    ∑ x ∈ range n, exp (-(2 * (π : ℂ) * I * (ℓ : ℂ) * (x : ℂ)) / (n : ℂ)) * f (x : ℤ)

/-- **Nielsen & Chuang, Exercise 5.20 (off-support).** For a period-`r` function `f` sampled over a
length `N` that is a multiple of `r`, the length-`N` Fourier coefficient vanishes at every frequency
`ℓ` that is not a multiple of `N / r`. -/
theorem normDFT_periodic_eq_zero (r N : ℕ) (hr : 0 < r) (hd : r ∣ N) (hN : 0 < N)
    (hf : Function.Periodic f (r : ℤ)) {ℓ : ℤ} (hℓ : ¬ (↑(N / r) : ℤ) ∣ ℓ) :
    normDFT N f ℓ = 0 := sorry

/-- **Nielsen & Chuang, Exercise 5.20 (on-support).** For a period-`r` function `f` sampled over a
length `N` that is a multiple of `r`, the length-`N` Fourier coefficient at a frequency `k · (N/r)`
equals `√(N/r)` times the length-`r` Fourier coefficient of `f` at `k` — i.e. the transform
`normDFT r f` of equation (5.63), up to the `√(N/r)` normalization. -/
theorem normDFT_periodic_mul (r N : ℕ) (hr : 0 < r) (hd : r ∣ N) (hN : 0 < N)
    (hf : Function.Periodic f (r : ℤ)) (k : ℤ) :
    normDFT N f (k * (↑(N / r) : ℤ)) = (Real.sqrt ((N / r : ℕ) : ℝ) : ℂ) * normDFT r f k := sorry
