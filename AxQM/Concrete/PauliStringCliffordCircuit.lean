/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCnotConjugation

/-!
# Concrete: elementary Clifford gates and circuits, and their action on Pauli strings

A **Clifford circuit** is a finite sequence of single-wire Hadamard/phase gates and two-wire `CNOT`
gates. Conjugating an `n`-qubit Pauli string (`Concrete.pauliString`, `g : Fin n → Fin 4`) by such
a circuit returns another Pauli string, up to a nonzero (`±1`) phase, whose **check matrix** is
obtained from `g`'s by applying, in order, each gate's elementary symplectic column operation. This
is the operator-level statement of Nielsen & Chuang **Problem 10.3**: *a circuit acts on the check
matrix by column operations*, and the encoding circuit of Eqs (10.124)→(10.125) is exactly such a
sequence.

## The gate and circuit

* `CliffordGate.toMatrix` — its unitary matrix;
* `CliffordGate.act` — its **phase-free action** on a Pauli string, i.e. how it transforms the
  check-matrix row;
* `CliffordGate.sign` — the `±1` phase acquired under conjugation.
-/

open Matrix

noncomputable section

namespace AxQM.Concrete

variable {n : ℕ}

/-- An **elementary Clifford gate** on the `n`-qubit register: the single-wire Hadamard (`had j`)
and phase (`phase j`) gates on wire `j`, and the two-wire controlled-NOT (`cnot c t h`) with control
`c`, target `t` (`h : c ≠ t`). These are the generators of the check-matrix column operations behind
the encoding circuit of Nielsen & Chuang Problem 10.3. -/
inductive CliffordGate (n : ℕ) where
  /-- The Hadamard gate on wire `j`. -/
  | had (j : Fin n)
  /-- The phase gate `S` on wire `j`. -/
  | phase (j : Fin n)
  /-- The controlled-NOT gate with control wire `c` and target wire `t` (`c ≠ t`). -/
  | cnot (c t : Fin n) (h : c ≠ t)

namespace CliffordGate

/-- The **unitary matrix** of an elementary Clifford gate: `kronWireGate j hadamardC` for `had j`,
`kronWireGate j sMatrix` for `phase j`, and `cnotWireGate c t` for `cnot c t`. -/
def toMatrix : CliffordGate n → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ
  | .had j => kronWireGate j hadamardC
  | .phase j => kronWireGate j sMatrix
  | .cnot c t _ => cnotWireGate c t

/-- The **phase-free action** of an elementary Clifford gate on a Pauli string `g : Fin n → Fin 4`,
i.e. how it transforms the check-matrix row. -/
def act : CliffordGate n → (Fin n → Fin 4) → (Fin n → Fin 4)
  | .had j, g => Function.update g j (hadamardPauli (g j))
  | .phase j, g => Function.update g j (phasePauli (g j))
  | .cnot c t _, g => cnotPauliString g c t

/-- The **`±1` phase** an elementary Clifford gate acquires when conjugating the Pauli string `g`:
`hadamardPauliSign (g j)` / `phasePauliSign (g j)` for the single-wire gates and
`cnotPauliSign (g c) (g t)` for `cnot c t`. -/
def sign : CliffordGate n → (Fin n → Fin 4) → ℂ
  | .had j, g => hadamardPauliSign (g j)
  | .phase j, g => phasePauliSign (g j)
  | .cnot c t _, g => cnotPauliSign (g c) (g t)

end CliffordGate

/-- A **Clifford circuit** on the `n`-qubit register: a finite sequence of elementary Clifford gates
(`CliffordGate n`). -/
abbrev CliffordCircuit (n : ℕ) := List (CliffordGate n)

namespace CliffordCircuit

/-- The **unitary matrix** of a Clifford circuit: the product of its gate matrices, with the head
applied last — `[].toMatrix = 1`, `(γ :: U).toMatrix = γ.toMatrix * U.toMatrix`. -/
def toMatrix : CliffordCircuit n → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ
  | [] => 1
  | γ :: U => γ.toMatrix * toMatrix U

/-- The **phase-free action** of a Clifford circuit on a Pauli string (its transformation of the
check-matrix row): apply the gates right-to-left — `[].act g = g`, `(γ :: U).act g = γ.act (U.act
g)`. This is the composed sequence of elementary symplectic column operations. -/
def act : CliffordCircuit n → (Fin n → Fin 4) → (Fin n → Fin 4)
  | [], g => g
  | γ :: U, g => γ.act (act U g)

end CliffordCircuit

end AxQM.Concrete

end
