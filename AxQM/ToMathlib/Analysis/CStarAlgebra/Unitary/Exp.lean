/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Every unitary matrix is the exponential of a Hermitian matrix

For a unitary `u` in a unital C⋆-algebra, `Unitary.argSelfAdjoint u = cfc arg u` is the selfadjoint
"argument" `-i log u`, and `selfAdjoint.expUnitary K = exp (i • K)`.

## Main results

* `CStarMatrix.expUnitary_argSelfAdjoint`: for every unitary matrix `u`,
  `selfAdjoint.expUnitary (Unitary.argSelfAdjoint u) = u`, with no restriction on the spectrum.
* `CStarMatrix.exists_expUnitary_eq_of_mem_unitary`: every unitary matrix `U` equals
  `selfAdjoint.expUnitary K = exp (i K)` for some Hermitian `K`.
-/

@[expose] public section

open Complex NormedSpace selfAdjoint Unitary
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Every unitary matrix is recovered from its argument.** For any unitary matrix `u`,
`selfAdjoint.expUnitary (Unitary.argSelfAdjoint u) = u`, i.e. `exp (i • (-i log u)) = u`, with no
hypothesis on the spectrum. -/
theorem CStarMatrix.expUnitary_argSelfAdjoint (u : unitary (CStarMatrix n n ℂ)) :
    selfAdjoint.expUnitary (Unitary.argSelfAdjoint u) = u := sorry

/-- **Nielsen & Chuang, Exercise 2.56.** Every unitary matrix `U` can be written as `exp (i K)` for
some Hermitian matrix `K`. -/
theorem CStarMatrix.exists_expUnitary_eq_of_mem_unitary
    {U : CStarMatrix n n ℂ} (hU : U ∈ unitary (CStarMatrix n n ℂ)) :
    ∃ K : selfAdjoint (CStarMatrix n n ℂ), (selfAdjoint.expUnitary K : CStarMatrix n n ℂ) = U :=
      sorry
