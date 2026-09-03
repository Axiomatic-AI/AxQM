/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Multilinear polynomials and the uniqueness of Boolean representations

A multivariate polynomial is *multilinear* when every variable occurs to degree at most one, i.e.
every monomial in its support is square-free. On the Boolean cube `{0, 1} ⊆ R` a multilinear
polynomial is determined by the function it computes: two multilinear polynomials that agree at
every point with all coordinates in `{0, 1}` are equal.

## Main results

* `MvPolynomial.IsMultilinear.eq_of_forall_eval_boolean`: two multilinear polynomials that agree
  at every Boolean point are equal — the *uniqueness of the multilinear representation* of a
  function `{0, 1}ˢ → R`.
-/

@[expose] public section

namespace MvPolynomial

variable {σ : Type*} {R : Type*}

section CommSemiring
variable [CommSemiring R]

/-- A multivariate polynomial is **multilinear** when every variable occurs to degree at most
one. -/
def IsMultilinear (p : MvPolynomial σ R) : Prop := ∀ i, p.degreeOf i ≤ 1

end CommSemiring

section CommRing
variable [CommRing R]

/-- **Uniqueness of the multilinear representation** (Nielsen & Chuang, Exercise 6.18): two
multilinear polynomials that agree at every point of the Boolean cube (every `x : σ → R` with each
coordinate in `{0, 1}`) are equal. Consequently a function `{0, 1}ˢ → R` has at most one
multilinear polynomial representing it. -/
theorem IsMultilinear.eq_of_forall_eval_boolean {p q : MvPolynomial σ R}
    (hp : p.IsMultilinear) (hq : q.IsMultilinear)
    (h : ∀ x : σ → R, (∀ i, x i = 0 ∨ x i = 1) → eval x p = eval x q) : p = q := sorry

end CommRing

end MvPolynomial
