/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic.Abel

/-!
# The anticommutator of two ring elements

For two elements `a` and `b` of a ring, this file defines their *anticommutator*
`anticommutator a b = a * b + b * a`, the symmetric counterpart of the commutator
`⁅a, b⁆ = a * b - b * a` (the Lie bracket on a ring, `Ring.lie_def`).

## Main definitions

* `anticommutator a b` : the anticommutator `a * b + b * a`.

## Main results

* `mul_eq_invOf_two_mul_lie_add_anticommutator` : in a ring in which `2` is invertible, the product
  is the half-sum `a * b = ⅟2 * (⁅a, b⁆ + anticommutator a b)`.
* `mul_eq_invOf_two_smul_lie_add_anticommutator` : the same decomposition for an algebra over a
  commutative (semi)ring in which `2` is invertible, with `1 / 2` acting as a scalar,
  `a * b = ⅟(2 : 𝕜) • (⁅a, b⁆ + anticommutator a b)`. This is the form matching Nielsen & Chuang's
  operators over `ℂ`, where the division by `2` is scalar division.
* `eq_zero_of_lie_eq_zero_of_anticommutator_eq_zero` : **Nielsen & Chuang, Exercise 2.44** — if
  moreover `a` is a unit, then `b = 0`.
-/

@[expose] public section

variable {A : Type*}

/-- The **anticommutator** `a * b + b * a` of two elements of a (non-unital, non-associative) ring;
the symmetric counterpart of the commutator (Lie bracket) `⁅a, b⁆ = a * b - b * a`. -/
def anticommutator [Mul A] [Add A] (a b : A) : A := a * b + b * a

/-- In a ring in which `2` is invertible, a product is the half-sum of the commutator and the
anticommutator: `a * b = ⅟2 * (⁅a, b⁆ + anticommutator a b)`. This is the ring form of
**Nielsen & Chuang, Exercise 2.42**. -/
theorem mul_eq_invOf_two_mul_lie_add_anticommutator [Ring A] [Invertible (2 : A)] (a b : A) :
    a * b = ⅟2 * (⁅a, b⁆ + anticommutator a b) := sorry

/-- For an algebra over a commutative (semi)ring in which `2` is invertible, a product is the
half-sum of the commutator and the anticommutator, with `1 / 2` acting as a scalar:
`a * b = ⅟(2 : 𝕜) • (⁅a, b⁆ + anticommutator a b)`. This is the form of
**Nielsen & Chuang, Exercise 2.42** matching their operators over `ℂ`, where the division by `2` is
scalar division. -/
theorem mul_eq_invOf_two_smul_lie_add_anticommutator
    {𝕜 : Type*} [CommSemiring 𝕜] [Ring A] [Algebra 𝕜 A] [Invertible (2 : 𝕜)] (a b : A) :
    a * b = ⅟(2 : 𝕜) • (⁅a, b⁆ + anticommutator a b) := sorry

/-- **Nielsen & Chuang, Exercise 2.44.** -/
theorem eq_zero_of_lie_eq_zero_of_anticommutator_eq_zero [Ring A] [Invertible (2 : A)] {a b : A}
    (hlie : ⁅a, b⁆ = 0) (hanti : anticommutator a b = 0) (ha : IsUnit a) : b = 0 := sorry

end
