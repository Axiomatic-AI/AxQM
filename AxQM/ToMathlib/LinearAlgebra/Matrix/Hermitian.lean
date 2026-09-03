/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The Kronecker product of Hermitian matrices

## Main results

* `Matrix.IsHermitian.kronecker`: **Nielsen & Chuang, Exercise 2.30** — the Kronecker product
  of two Hermitian matrices is Hermitian.

-/

@[expose] public section

namespace Matrix

section
variable {α β m n : Type*} {A : Matrix n n α}
open scoped Kronecker
variable [CommMagma α] [StarMul α]

/-- The Kronecker product of two Hermitian matrices is Hermitian.

This is Nielsen & Chuang, Exercise 2.30 (*the tensor product of two Hermitian operators is
Hermitian*). Commutativity of the entries is needed because `star` is an
anti-homomorphism. -/
theorem IsHermitian.kronecker {A : Matrix m m α} {B : Matrix n n α} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := sorry

end

end Matrix
