/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Data.Nat.Size
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Perfect powers of natural numbers

A natural number `n` is a *perfect power* when `n = a ^ b` for some base `a ≥ 1` and exponent
`b ≥ 2`. This file defines the predicate `Nat.IsPerfectPower`, proves the key finiteness fact that
bounds any nontrivial exponent by the bit length `Nat.size n`, deduces that perfect-power-ness is
equivalent to a *finite* search over exponents, and packages this as a `Decidable` instance — an
explicit decision procedure.

## Main results

* `Nat.IsPerfectPower` — the predicate `∃ a b, 1 ≤ a ∧ 2 ≤ b ∧ a ^ b = n`.
* `Nat.exponent_lt_size` — if `a ^ b = n` with a nontrivial base `2 ≤ a`, then `b < n.size`. Hence
  the only exponents that can witness a perfect power of `n` are those below `L = n.size`, the
  number of bits of `n`.
* `Nat.isPerfectPower_iff` — for every `n`, `n.IsPerfectPower` holds iff `n = 1` or there is an
  exponent `b ∈ Finset.Ico 2 n.size` and a base `a` with `a ^ b = n`. The unbounded double
  existential of the definition is thus equivalent to a bounded, finite one.
* `Nat.instDecidableIsPerfectPower` — decidability of `Nat.IsPerfectPower`.
-/

public section

namespace Nat

/-- A natural number `n` is a *perfect power* when `n = a ^ b` for some base `a ≥ 1` and exponent `b
≥ 2`. This is the property Nielsen & Chuang's Exercise 5.17 decides. -/
def IsPerfectPower (n : ℕ) : Prop := ∃ a b, 1 ≤ a ∧ 2 ≤ b ∧ a ^ b = n

/-- **Exponent bound (Exercise 5.17, part 1).** If `n = a ^ b` with a nontrivial base `2 ≤ a`, then
the exponent `b` is strictly less than the bit length `n.size` of `n`. Consequently only
finitely many exponents — those below `n.size` — can witness a perfect-power representation of
`n`.
-/
theorem exponent_lt_size {n a b : ℕ} (ha : 2 ≤ a) (hab : a ^ b = n) : b < n.size := by
  rw [Nat.lt_size]
  calc 2 ^ b ≤ a ^ b := Nat.pow_le_pow_left ha b
    _ = n := hab

/-- **Correctness of the bounded search (Exercise 5.17).** A natural number is a perfect power iff
it equals `1`, or it is `a ^ b` for some base `a` and some exponent `b` in the finite range
`Finset.Ico 2 n.size`. -/
theorem isPerfectPower_iff (n : ℕ) :
    n.IsPerfectPower ↔ n = 1 ∨ ∃ b ∈ Finset.Ico 2 n.size, ∃ a, a ^ b = n := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    rcases Nat.lt_or_ge a 2 with hlt | hge
    · left
      have h1 : a = 1 := by omega
      subst h1
      simpa using hab.symm
    · exact Or.inr ⟨b, Finset.mem_Ico.2 ⟨hb, exponent_lt_size hge hab⟩, a, hab⟩
  · rintro (rfl | ⟨b, hb, a, hab⟩)
    · exact ⟨1, 2, le_refl 1, le_refl 2, one_pow 2⟩
    · rw [Finset.mem_Ico] at hb
      have hpos : 0 < n := Nat.size_pos.1 (lt_of_le_of_lt (Nat.zero_le b) hb.2)
      have ha : 1 ≤ a := by
        rcases Nat.eq_zero_or_pos a with rfl | h
        · rw [zero_pow (show b ≠ 0 by omega)] at hab; omega
        · exact h
      exact ⟨a, b, ha, hb.1, hab⟩

/-- **The decision procedure (Exercise 5.17, part 4).** Perfect-power-ness is decidable. -/
instance instDecidableIsPerfectPower (n : ℕ) : Decidable n.IsPerfectPower :=
  decidable_of_iff _ (isPerfectPower_iff n).symm

end Nat
