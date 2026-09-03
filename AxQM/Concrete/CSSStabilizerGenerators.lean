/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrixSymplectic
import AxQM.ToMathlib.InformationTheory.Coding.DualCode

/-!
# Concrete: the CSS stabilizer generators `X^v`, `Z^u`

The two families of stabilizer generators that make up the CSS check matrix (10.106) of
**Nielsen & Chuang, Exercise 10.51** (p. 470).
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- The **`X`-type Pauli string** `X^v = X^{v₁} ⊗ ⋯ ⊗ X^{vₙ}` of a binary support vector
`v : Fin n → ZMod 2`: the Pauli string with an `X` (index `1`) on each qubit `k` where `v k = 1`,
and the identity (index `0`) elsewhere. These are the `X`-type stabilizer generators of a CSS
code — the rows of the top block `H(C₂⊥)` of the check matrix (10.106). -/
def xString (v : Fin n → ZMod 2) : Fin n → Fin 4 := fun k => if v k = 1 then 1 else 0

/-- The **`Z`-type Pauli string** `Z^u = Z^{u₁} ⊗ ⋯ ⊗ Z^{uₙ}` of a binary support vector
`u : Fin n → ZMod 2`: the Pauli string with a `Z` (index `3`) on each qubit `k` where `u k = 1`,
and the identity (index `0`) elsewhere. These are the `Z`-type stabilizer generators of a CSS
code — the rows of the bottom block `H(C₁)` of the check matrix (10.106). -/
def zString (u : Fin n → ZMod 2) : Fin n → Fin 4 := fun k => if u k = 1 then 3 else 0

end AxQM.Concrete
