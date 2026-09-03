/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCommutation

/-!
# Concrete: a standard-register Pauli string is an involution (`P_g² = I`)

The Pauli string `pauliStringStd g` on the flat computational-basis register `Fin (2ⁿ)` squares to
the identity.
-/

open scoped Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-- **A standard-register Pauli string is an involution**: `pauliStringStd g · pauliStringStd g =
I`. -/
theorem pauliStringStd_mul_self (g : Fin n → Fin 4) :
    pauliStringStd g * pauliStringStd g = 1 := by
  unfold pauliStringStd
  rw [Matrix.submatrix_mul_equiv, pauliString_mul_self, Matrix.submatrix_one_equiv]

end AxQM.Concrete
