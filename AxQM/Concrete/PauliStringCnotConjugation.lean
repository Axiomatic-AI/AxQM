/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCliffordConjugation
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Concrete: two-wire CNOT conjugation of Pauli strings

This file sets up the **two-wire
Clifford generator** — the controlled-NOT gate `CNOT` with control wire `c` and target wire `t` of
an `n`-qubit register — together with the single-pair tableau describing how it acts on a Pauli
string (`Concrete.pauliString`, `g : Fin n → Fin 4`) by **conjugation**.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- The **CNOT bit-permutation** with control wire `c` and target wire `t`: flip the target bit `x
t` by the control bit `x c`, `x ↦ update x t (x t + x c)` (in `Fin 2`, i.e. mod 2). This is the
action of `CNOT_{c→t}` on the computational-basis register `Fin n → Fin 2`, `|x⟩ ↦ |x_t ⊕ x_c on
wire t⟩`. -/
def cnotPerm (c t : Fin n) (x : Fin n → Fin 2) : Fin n → Fin 2 :=
  Function.update x t (x t + x c)

/-- The **CNOT gate** `CNOT_{c→t}` (control wire `c`, target wire `t`) on the `n`-qubit register, as
the **permutation matrix** of the bit-permutation `cnotPerm c t`: `(i, j)` entry is `1` iff `i =
cnotPerm c t j`, else `0`. -/
def cnotWireGate (c t : Fin n) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun i j => if i = cnotPerm c t j then (1 : ℂ) else 0

/-- The **new control Pauli** in `CNOT (σ_a^c ⊗ σ_b^t) CNOT†`, as a function of the control index
`a` and target index `b` (`0 = I, 1 = X, 2 = Y, 3 = Z`). -/
def cnotCtrlPauli : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 3, 3], ![1, 1, 2, 2], ![2, 2, 1, 1], ![3, 3, 0, 0]]

/-- The **new target Pauli** in `CNOT (σ_a^c ⊗ σ_b^t) CNOT†`. The target's `Z`-bit is unchanged and
its `X`-bit gains the control's (`x_t ↦ x_t + x_c`), so it depends on both `a` and `b`. -/
def cnotTgtPauli : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![1, 0, 3, 2], ![0, 1, 2, 3]]

/-- The **sign** `ε` in the CNOT pair tableau
`CNOT (σ_a^c ⊗ σ_b^t) CNOT† = ε • (σ_{a'}^c ⊗ σ_{b'}^t)`. It is `-1` exactly for the pairs
`(X_c, Z_t)` and `(Y_c, Y_t)`, and `+1` otherwise. -/
def cnotPauliSign : Fin 4 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1], ![1, 1, 1, -1], ![1, 1, -1, 1], ![1, 1, 1, 1]]

/-- The **CNOT-transformed Pauli string**: `CNOT_{c→t}` conjugation changes only wire `c` (to
`cnotCtrlPauli (g c) (g t)`) and wire `t` (to `cnotTgtPauli (g c) (g t)`), leaving every other
wire fixed. -/
def cnotPauliString (g : Fin n → Fin 4) (c t : Fin n) : Fin n → Fin 4 :=
  Function.update (Function.update g t (cnotTgtPauli (g c) (g t))) c (cnotCtrlPauli (g c) (g t))

end AxQM.Concrete
