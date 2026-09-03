/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # An integral bound on `∑ 1/q²` over the integers `≥ 2` and over the primes

This file records an elementary integral-comparison bound on the tail of the series `∑ 1/q²`, and
the bound `∑_{p prime} 1/p² ≤ 3/4` for the sub-sum over the primes.

## Main statements

* `two_div_three_mul_sq_le_integral_one_div_sq`: for `x ≥ 2`, `2/(3 x²) ≤ ∫_x^{x+1} 1/y² dy`
  (the exercise's first claim; equality holds at `x = 2`).
* `integral_Ioi_one_div_sq_two`: `∫_2^∞ 1/y² dy = 1/2`.
* `Nat.Primes.tsum_one_div_sq_le`: `∑_{p prime} 1/p² ≤ 3/4` (the version used for N&C eq. (5.58)).
-/

open scoped MeasureTheory
open intervalIntegral

@[expose] public section

/-- **Nielsen & Chuang, Exercise 5.16 (first claim).** For every `x ≥ 2`,
`2 / (3 x²) ≤ ∫_x^{x+1} 1/y² dy`, with equality at `x = 2`. -/
theorem two_div_three_mul_sq_le_integral_one_div_sq {x : ℝ} (hx : 2 ≤ x) :
    2 / (3 * x ^ 2) ≤ ∫ y in x..(x + 1), 1 / y ^ 2 := sorry

/-- The improper integral `∫_2^∞ 1/y² dy = 1/2`. -/
theorem integral_Ioi_one_div_sq_two : ∫ y in Set.Ioi (2 : ℝ), 1 / y ^ 2 = 1 / 2 := sorry

/-- **Nielsen & Chuang, Exercise 5.16 (second claim, prime form).**
`∑_{p prime} 1/p² ≤ 3/4`. This is the version used in N&C to bound the failure probability in
eq. (5.58). -/
theorem Nat.Primes.tsum_one_div_sq_le : ∑' p : Nat.Primes, 1 / ((p : ℕ) : ℝ) ^ 2 ≤ 3 / 4 := sorry

end
