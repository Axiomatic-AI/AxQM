/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The Kronecker product under entrywise `star`

## Main results

* `Matrix.map_star_kronecker`: `star` applied entrywise distributes over the Kronecker
  product.

-/

@[expose] public section

namespace Matrix

section
open scoped RightActions
variable {R S α α' β β' γ γ' : Type*}
variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}
open Matrix
open Kronecker

/-- Entrywise `star` (complex conjugation of each entry) distributes over the Kronecker
product. -/
theorem map_star_kronecker [CommMagma R] [StarMul R] (x : Matrix l m R) (y : Matrix n p R) :
    (x ⊗ₖ y).map star = x.map star ⊗ₖ y.map star := sorry

end

end Matrix
