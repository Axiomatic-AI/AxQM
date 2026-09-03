/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.Divisors

/-!
# Nontrivial square roots of one reveal a factor

A *nontrivial square root of one* modulo `N` is a residue `x` with `x² ≡ 1 (mod N)` that is
neither `1` nor `-1`.  This file proves the elementary number-theoretic fact — the mathematical
heart of the reduction of factoring to order-finding (Shor's algorithm) — that from such an `x`
one immediately reads off a *nontrivial factor* of `N`: at least one of `gcd(x - 1, N)` and
`gcd(x + 1, N)` is one.

## Main definitions

* `Nat.IsNontrivialFactor d n` : `d` is a divisor of `n` strictly between `1` and `n` (equivalently,
  `d ∈ n.properDivisors` with `1 < d`).

## Main results

* `Nat.isNontrivialFactor_gcd_sub_one_or_gcd_add_one_of_sq_modEq_one` : **Nielsen & Chuang,
  Theorem 5.2** (and Theorem A4.11): at least one of `gcd(x - 1, N)`, `gcd(x + 1, N)` is a
  nontrivial factor of `N`.
-/

@[expose] public section

namespace Nat

/-- `d` is a *nontrivial factor* of `n`: a divisor of `n` strictly between `1` and `n`.
Equivalently, `d ∈ n.properDivisors` together with `1 < d`. -/
def IsNontrivialFactor (d n : ℕ) : Prop := d ∣ n ∧ 1 < d ∧ d < n

/-- **Nielsen & Chuang, Theorem 5.2** (equivalently Theorem A4.11 in Appendix 4). If `x` is a
nontrivial square root of `1` modulo `N`, then at least one of `gcd(x - 1, N)` and `gcd(x + 1, N)`
is a nontrivial factor of `N`. -/
theorem isNontrivialFactor_gcd_sub_one_or_gcd_add_one_of_sq_modEq_one {N x : ℕ} (hN : 0 < N)
    (hx : 1 ≤ x) (hsq : x ^ 2 ≡ 1 [MOD N]) (h1 : ¬ x ≡ 1 [MOD N])
    (h2 : ¬ x + 1 ≡ 0 [MOD N]) :
    IsNontrivialFactor (Nat.gcd (x - 1) N) N ∨ IsNontrivialFactor (Nat.gcd (x + 1) N) N := sorry

end Nat
