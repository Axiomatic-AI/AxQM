/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# The submodule stabilized by a set of endomorphisms

Given a set `S` of endomorphisms of a module `M`, the vectors that are fixed by *every* element of
`S` form a submodule of `M`. This file introduces that submodule and records its two basic
descriptions.

## Main definitions

* `Module.End.stabilizedSubmodule S`: the submodule `{v | ∀ f ∈ S, f v = v}` of vectors fixed by
  every endomorphism in `S`.

## Main results

* `Module.End.smul_add_smul_mem_stabilizedSubmodule`: `stabilizedSubmodule S` is closed under linear
  combinations of pairs of its elements — the concrete form of it being a submodule.
* `Module.End.stabilizedSubmodule_eq_iInf_eigenspace_one`: `stabilizedSubmodule S` is the
  intersection of the eigenvalue-`1` eigenspaces of the elements of `S`.
-/

@[expose] public section

namespace Module.End

section Semiring

variable {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/-- The submodule stabilized by a set `S` of endomorphisms of `M`: the vectors fixed by every
element of `S`. -/
def stabilizedSubmodule (S : Set (Module.End R M)) : Submodule R M where
  carrier := {v | ∀ f ∈ S, f v = v}
  add_mem' {a b} ha hb f hf := by rw [map_add, ha f hf, hb f hf]
  zero_mem' f _ := map_zero f
  smul_mem' c a ha f hf := by rw [map_smul, ha f hf]

/-- An arbitrary linear combination `c • a + d • b` of two elements `a, b` of the stabilized
submodule `V_S` again lies in `V_S`; hence `V_S` is a subspace of `M`. This is the first part of
Nielsen & Chuang, Exercise 10.29. -/
theorem smul_add_smul_mem_stabilizedSubmodule (S : Set (Module.End R M)) {a b : M}
    (ha : a ∈ stabilizedSubmodule S) (hb : b ∈ stabilizedSubmodule S) (c d : R) :
    c • a + d • b ∈ stabilizedSubmodule S := sorry

end Semiring

end Module.End

section CommRing

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

namespace Module.End

/-- The stabilized submodule `V_S` is the intersection of the eigenvalue-`1` eigenspaces of the
elements of `S`. This is the second part of Nielsen & Chuang, Exercise 10.29. -/
theorem stabilizedSubmodule_eq_iInf_eigenspace_one (S : Set (Module.End R M)) :
    stabilizedSubmodule S = ⨅ f ∈ S, Module.End.eigenspace f 1 := sorry

end Module.End

end CommRing
