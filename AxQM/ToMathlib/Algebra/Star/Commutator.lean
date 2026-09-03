/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Star (adjoint) and the commutator

For elements `a` and `b` of a star ring, this file records how the star (adjoint) operation
interacts with the commutator `⁅a, b⁆ = a * b - b * a` (the Lie bracket on a ring).

## Main results

* `star_lie` : the adjoint reverses the commutator, `star ⁅a, b⁆ = ⁅star b, star a⁆`, in any
  (non-unital, non-associative) star ring.
* `isSelfAdjoint_smul_commutator` : scaling the commutator of two self-adjoint elements by a
  skew-adjoint scalar `s` produces a self-adjoint element, `IsSelfAdjoint (s • ⁅A, B⁆)` — the
  scalar-generalised form of Exercise 2.47.
-/

@[expose] public section

/-- The **adjoint of a commutator** is the commutator of the adjoints, with the order reversed:
`star ⁅a, b⁆ = ⁅star b, star a⁆`.

This is **Nielsen & Chuang, Exercise 2.45**, `[A, B]† = [B†, A†]`: `A` and `B` are operators on
a Hilbert space, which form a star ring under the adjoint `†`.
-/
theorem star_lie {R : Type*} [NonUnitalNonAssocRing R] [StarRing R] (a b : R) :
    star ⁅a, b⁆ = ⁅star b, star a⁆ := sorry

/-- Scaling the commutator `⁅A, B⁆` of two self-adjoint elements of a star ring by a skew-adjoint
scalar `s` yields a self-adjoint element: `IsSelfAdjoint (s • ⁅A, B⁆)`. -/
theorem isSelfAdjoint_smul_commutator {S R : Type*} [Ring S] [NonUnitalNonAssocRing R]
    [Module S R] [StarAddMonoid S] [StarRing R] [StarModule S R] {s : S}
    (hs : s ∈ skewAdjoint S) {A B : R} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (s • ⁅A, B⁆) := sorry
