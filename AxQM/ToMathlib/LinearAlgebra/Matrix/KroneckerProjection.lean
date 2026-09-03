/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Algebra.Star.StarProjection
public import AxQM.ToMathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The Kronecker product of two star projections is a star projection

A **star projection** (`IsStarProjection`) is a self-adjoint idempotent — exactly Nielsen &
Chuang's notion of a *projector* (*Quantum Computation and Quantum Information*, §2.1.5 / Box 2.2):
an operator `P` with `P† = P` and `P² = P`. In the concrete matrix picture the tensor product of
two operators is the **Kronecker product** `A ⊗ₖ B` (N&C eq. (2.50)), so this file proves that the
Kronecker product of two projectors is again a projector — **Nielsen & Chuang, Exercise 2.32**.

## Main results

* `IsStarProjection.kronecker`: **Nielsen & Chuang, Exercise 2.32** — the Kronecker product of two
  star projections is a star projection.
-/

@[expose] public section

open scoped Kronecker Matrix

variable {α : Type*} {m n : Type*}

/-- **Nielsen & Chuang, Exercise 2.32.** The Kronecker product `A ⊗ₖ B` of two star projections
(self-adjoint idempotents) is a star projection. -/
theorem IsStarProjection.kronecker [Fintype m] [Fintype n] [CommSemiring α] [StarRing α]
    {A : Matrix m m α} {B : Matrix n n α} (hA : IsStarProjection A) (hB : IsStarProjection B) :
    IsStarProjection (A ⊗ₖ B) := sorry

end
