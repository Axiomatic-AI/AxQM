/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliGroup
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Concrete: normalizer and centralizer of a Pauli subgroup (Nielsen & Chuang, Exercises 10.43–10.44)

Nielsen & Chuang **Exercise 10.43** (p. 465) and **Exercise 10.44** (p. 466).

## Main results
* `stabilizer_le_normalizer` — **Exercise 10.43** (group form): `S ≤ N(S)`, i.e. every subgroup of
  `Gₙ` lies in its normalizer.
* `mem_stabilizer_conjTranspose` — **Exercise 10.43** (N&C's literal dagger form): for `E ∈ S` and
  `g ∈ S`, `E g E† ∈ S`, i.e. `(toMat E)(toMat g)(toMat E)ᴴ = toMat h` for some `h ∈ S`.
* `normalizer_eq_centralizer_of_negOne_notMem` — **Exercise 10.44**: for `S ≤ Gₙ` with `-I ∉ S`,
  `N(S) = Z(S)` (`Subgroup.normalizer ↑S = Subgroup.centralizer ↑S`).
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-- **Exercise 10.43** (group form). Every subgroup `S` of the Pauli group `Gₙ` is contained in its
normalizer `N(S) = Subgroup.normalizer S`. This is the exercise in the `Subgroup.normalizer`
reading of `N(S)`. -/
theorem stabilizer_le_normalizer (S : Subgroup (PauliGroup n)) :
    S ≤ Subgroup.normalizer (S : Set (PauliGroup n)) := sorry

/-- **Exercise 10.43** (N&C's literal form). For a subgroup `S` of `Gₙ`, every `E ∈ S` normalizes
`S` in N&C's sense: `E g E† ∈ S` for all `g ∈ S`. At the matrix level, `(toMat E)(toMat g)(toMat
E)ᴴ = toMat h` for some `h ∈ S`. -/
theorem mem_stabilizer_conjTranspose {S : Subgroup (PauliGroup n)} {E : PauliGroup n} (hE : E ∈ S)
    {g : PauliGroup n} (hg : g ∈ S) :
    ∃ h ∈ S, E.toMat * g.toMat * E.toMat.conjTranspose = h.toMat := sorry

/-- **Exercise 10.44.** For any subgroup `S` of the Pauli group `Gₙ` with `-I ∉ S`, the normalizer
and the centralizer coincide: `N(S) = Z(S)`, i.e.
`Subgroup.normalizer ↑S = Subgroup.centralizer ↑S`.
-/
theorem normalizer_eq_centralizer_of_negOne_notMem {S : Subgroup (PauliGroup n)}
    (hS : PauliGroup.negOne n ∉ S) :
    Subgroup.normalizer (S : Set (PauliGroup n))
      = Subgroup.centralizer (S : Set (PauliGroup n)) := sorry

end AxQM.Concrete
