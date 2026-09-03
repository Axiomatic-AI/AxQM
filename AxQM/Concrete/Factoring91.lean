/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.ToMathlib.NumberTheory.PerfectPower
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Concrete: factoring `91` by reduction to order-finding (`x = 4`)

Nielsen & Chuang, Exercise 5.18 (§5.3.2, p. 234): *"Factoring 91."* This works the reduction of
factoring to order-finding (the algorithm on p. 233–234, built on Theorems 5.2 and 5.3) on the
concrete input `N = 91`, with the random element `x = 4`. Each step of the algorithm is confirmed.
-/

namespace AxQM.Concrete

/-- **Step 1 of the factoring algorithm passes for `N = 91`.** `91` is odd, so the "if `N` is even,
return the factor `2`" step returns no factor. -/
theorem ninetyOne_odd : Odd (91 : ℕ) := sorry

/-- **Step 2 of the factoring algorithm passes for `N = 91`.** `91` is not a perfect power `aᵇ`
(`a ≥ 1`, `b ≥ 2`), so the "if `N = aᵇ` return the base `a`" step returns no factor. The predicate
`Nat.IsPerfectPower` is precisely the property Step 2 decides. -/
theorem ninetyOne_not_isPerfectPower : ¬ Nat.IsPerfectPower 91 := sorry

/-- **The order `r` of `4` modulo `91` is `6`** (Step 4, order-finding): `6` is the least positive
integer with `4⁶ ≡ 1 (mod 91)`, i.e. the multiplicative order of the residue `4` in `ZMod 91`.
-/
theorem orderOf_four_zmod_ninetyOne : orderOf (4 : ZMod 91) = 6 := sorry

/-- **`x^{r/2} = 4³ = 64 (mod 91)`.** With `r = 6` the algorithm forms `x^{r/2}`; here it is the
residue `64`. -/
theorem four_pow_half_order_zmod_ninetyOne :
    (4 : ZMod 91) ^ (orderOf (4 : ZMod 91) / 2) = 64 := sorry

/-- **Step 5 success condition:** `x^{r/2} = 64 ≢ -1 (mod 91)`, so the algorithm succeeds rather
than failing. It is also `≠ 1`, so `64` is the promised non-trivial square root of `1`. -/
theorem four_pow_half_order_ne_neg_one_zmod_ninetyOne :
    (4 : ZMod 91) ^ (orderOf (4 : ZMod 91) / 2) ≠ -1 := sorry

/-- **The factor from `gcd(x^{r/2} - 1, N)`.** `gcd(4³ - 1, 91) = gcd(63, 91) = 7`, a non-trivial
factor of `91`. -/
theorem gcd_four_pow_half_order_pred_ninetyOne :
    Nat.gcd (4 ^ (orderOf (4 : ZMod 91) / 2) - 1) 91 = 7 := sorry

end AxQM.Concrete
