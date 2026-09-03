/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# A Hermitian involution is unitary

Over a commutative `*`-ring, a square matrix `A` that is Hermitian (`Aᴴ = A`) and squares to the
identity (`A * A = 1`) is unitary.

## Main results

* `Matrix.IsHermitian.mem_unitaryGroup`: a Hermitian matrix with `A * A = 1` is unitary.
-/

@[expose] public section

namespace Matrix

variable {n : Type*} [DecidableEq n] [Fintype n] {α : Type*} [CommRing α] [StarRing α]

/-- A Hermitian matrix that is its own inverse (`A * A = 1`) is unitary. -/
theorem IsHermitian.mem_unitaryGroup {A : Matrix n n α} (hH : A.IsHermitian) (hI : A * A = 1) :
    A ∈ Matrix.unitaryGroup n α := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hH.eq]
  exact hI

end Matrix
