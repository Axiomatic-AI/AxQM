/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCommutation

/-!
# Concrete: single-wire Clifford conjugation of Pauli strings and check-matrix column operations

This file establishes how the **single-wire Clifford generators** — the Hadamard gate `H` and the
phase gate `S` placed on one qubit of an `n`-qubit register — act on a Pauli string
(`Concrete.pauliString`, `g : Fin n → Fin 4`) by **conjugation**, and how that conjugation acts on
the string's **binary symplectic check-matrix** row (the `(x | z)` bits `pauliXBit`, `pauliZBit`).
Conjugating a Pauli string by a Clifford gate returns another Pauli string (up to a `±1` phase), and
on the check matrix this is exactly an **elementary symplectic column operation**.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- The **Hadamard tableau** on a Pauli index: `I, X, Y, Z ↦ I, Z, Y, X` (`0,1,2,3 ↦ 0,3,2,1`). It
records the Pauli that `H σ_a H` produces, up to sign (`hadamardPauliSign`): `H` exchanges the
`x̂` and `ẑ` Bloch axes and fixes `ŷ`. -/
def hadamardPauli : Fin 4 → Fin 4 := ![0, 3, 2, 1]

/-- The **sign** in the Hadamard tableau `H σ_a H = hadamardPauliSign a • σ_{hadamardPauli a}`: `-1`
for `a = Y` (since `H Y H = -Y`) and `+1` otherwise. -/
def hadamardPauliSign : Fin 4 → ℂ := ![1, 1, -1, 1]

/-- The **phase-gate tableau** on a Pauli index: `I, X, Y, Z ↦ I, Y, X, Z` (`0,1,2,3 ↦ 0,2,1,3`). It
records the Pauli that `S σ_a S†` produces, up to sign (`phasePauliSign`): the phase gate `S =
diag(1, i)` rotates `X ↦ Y` and `Y ↦ X` and fixes `Z`. -/
def phasePauli : Fin 4 → Fin 4 := ![0, 2, 1, 3]

/-- The **sign** in the phase-gate tableau `S σ_a S† = phasePauliSign a • σ_{phasePauli a}`: `-1`
for `a = Y` (since `S Y S† = -X`) and `+1` otherwise. -/
def phasePauliSign : Fin 4 → ℂ := ![1, 1, -1, 1]

/-- The single-qubit gate `G` placed on **wire `j`** of the `n`-qubit register `Fin n → Fin 2`
(identity on every other wire). -/
def kronWireGate (j : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  kronFamily (Function.update (fun _ => 1) j G)

end AxQM.Concrete
