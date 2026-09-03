/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Algebra.Group.Pi.Units

/-!
# The order-finding reduction: most units modulo an odd `N` are good for factoring

For an odd modulus `N > 1`, this file bounds — as an exact cardinality inequality over the unit
group `(ZMod N)ˣ` — the fraction of units `x` that are **good** for the reduction of factoring to
order-finding: those whose multiplicative order `r = orderOf x` is even and satisfy
`x ^ (r / 2) ≠ -1`.  Writing `m := N.primeFactors.card` for the number of distinct prime factors,
the bound is `(2^(m-1) - 1) · φ(N) ≤ 2^(m-1) · #{good units}`.

## Main results

* `ZMod.orderFinding_good_units_card_ge` : the corrected cardinality bound displayed above.
* `ZMod.not_orderFinding_good_units_printed_bound` : the refutation — the printed bound
  `1 - 1/2^m` fails.
-/

@[expose] public section

open Finset

namespace ZMod

/-- **Corrected Nielsen & Chuang Theorem 5.3 (= Theorem A4.13), as a cardinality bound.**

`(2 ^ (m - 1) - 1) * φ(N) ≤ 2 ^ (m - 1) * #{good units}`.

Interpreting the uniform choice of a random unit, the probability of drawing a good unit is
`#{good}/φ(N) ≥ 1 - 1/2^{m-1}`. (Nielsen & Chuang print `1 - 1/2^m`; that bound is an erratum.)
-/
theorem orderFinding_good_units_card_ge {N : ℕ} [NeZero N] (hN : Odd N) (hN1 : 1 < N) :
    (2 ^ (N.primeFactors.card - 1) - 1) * N.totient ≤
      2 ^ (N.primeFactors.card - 1) *
        #{x : (ZMod N)ˣ | Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1} := sorry

/-- **Nielsen & Chuang's Theorem 5.3 is false as printed.** The book states the good-unit fraction
is `≥ 1 - 1/2^m` (their eq. (5.60) / (A4.32)), which as a cardinality bound reads
`(2^m - 1) * φ(N) ≤ 2^m * #{good units}` for every odd `N > 1` with `m` distinct prime
factors. The corrected
bound `1 - 1/2^{m-1}` (`ZMod.orderFinding_good_units_card_ge`) holds and is tight. -/
theorem not_orderFinding_good_units_printed_bound :
    ¬ ∀ (N : ℕ) [NeZero N], Odd N → 1 < N →
      (2 ^ N.primeFactors.card - 1) * N.totient ≤
        2 ^ N.primeFactors.card *
          #{x : (ZMod N)ˣ | Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1} := sorry

end ZMod
