/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledUnitary

/-!
# AxQM.Basic.API — CNOT as a permutation of the density matrix (N&C Ex 4.19)

The operator-level form of Nielsen & Chuang's Exercise 4.19: the action of the `CNOT` gate on a
two-qubit *density matrix* `ρ`, written out explicitly in the computational basis.

## Main declarations
* `State.twoQubitStdMatrix` — the **density matrix** of a two-qubit state in the computational
  product basis `{|i⟩ ⊗ |j⟩}` (indexed by `Fin 2 × Fin 2`), whose `(i, j)` entry is
  `⟨i|ρ|j⟩ = ⟪|i⟩, ρ|j⟩⟫`. The density-operator analogue of `Evolution.twoQubitStdMatrix`
  (N&C Ex 4.16).
* `cnotBasisPerm` — the permutation of the computational basis `(c, t) ↦ (c, t ⊕ c)` induced by
  `CNOT`, as an `Equiv.Perm (Fin 2 × Fin 2)` (`CNOT` "is a simple permutation"); it is the
  transposition swapping `|10⟩` and `|11⟩`, fixing `|00⟩` and `|01⟩`.
* `cnotGate_evolve_twoQubitStdMatrix` — **Exercise 4.19:** the density matrix of `CNOT ρ CNOT†` is
  the density matrix of `ρ` with its rows and columns reindexed by `cnotBasisPerm`:
  `(CNOT.evolve ρ).twoQubitStdMatrix = ρ.twoQubitStdMatrix.submatrix cnotBasisPerm cnotBasisPerm`,
  i.e. entrywise `⟨(c,t)|CNOT ρ CNOT†|(c',t')⟩ = ⟨(c, t⊕c)|ρ|(c', t'⊕c')⟩`.
-/

open scoped InnerProductSpace TensorProduct

open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- The **computational-basis density matrix** of a two-qubit state `ρ`. -/
def State.twoQubitStdMatrix (ρ : State (qubit ⊗ qubit)) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j => inner ℂ (qubitBasis i.1 ⊗ qubitBasis i.2).vec
    (ρ.op (qubitBasis j.1 ⊗ qubitBasis j.2).vec)

/-- The permutation of the two-qubit computational basis induced by `CNOT`,
`(c, t) ↦ (c, t ⊕ c)` (addition in `Fin 2`), as a genuine `Equiv.Perm (Fin 2 × Fin 2)`. It is an
involution — `CNOT` flips the target twice back to itself — so it is its own inverse. This encodes
N&C's statement that `CNOT` "is a simple permutation" of the density-matrix elements. -/
def cnotBasisPerm : Equiv.Perm (Fin 2 × Fin 2) :=
  Function.Involutive.toPerm (fun p => (p.1, p.2 + p.1)) fun p => by
    obtain ⟨a, b⟩ := p
    have : b + a + a = b := by fin_cases a <;> fin_cases b <;> decide
    simp [this]

/-- **Nielsen & Chuang, Exercise 4.19.** Since `cnotBasisPerm` is the transposition `|10⟩ ↔ |11⟩`,
the concrete effect is to swap the third and fourth rows, and the third and fourth columns, of the
density matrix. -/
theorem cnotGate_evolve_twoQubitStdMatrix (ρ : State (qubit ⊗ qubit)) :
    (cnotGate.evolve ρ).twoQubitStdMatrix
      = ρ.twoQubitStdMatrix.submatrix cnotBasisPerm cnotBasisPerm := sorry

end AxQM
