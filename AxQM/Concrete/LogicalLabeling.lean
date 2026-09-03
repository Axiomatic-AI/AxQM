/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TemporalLabeling

/-!
# Logical labeling: the population-permutation circuit (Nielsen & Chuang, Exercise 7.43)

*Logical labeling* (§7.7.1, p. 334–335) prepares an *effective pure state* on an NMR ensemble of
three nearly identical spins in a single experiment. Starting from the three-spin deviation
density matrix `ρ` of N&C (7.162), a permutation circuit `P` produces the state `ρ'` of (7.164).

## The circuit

* `logicalLabelCCNot01`, `logicalLabelCCNot10` — two doubly-controlled-NOTs flipping the first qubit
  conditioned on the last two (`|001⟩ ↔ |101⟩` for `(q₁, q₂) = (0, 1)`, `|010⟩ ↔ |110⟩` for
  `(q₁, q₂) = (1, 0)`);
* `logicalLabelCFlip` — conditioned on the first qubit being `|1⟩`, the involution that exchanges
  `|00⟩ ↔ |11⟩` of the last two qubits while fixing `|01⟩, |10⟩` (flip *both* last qubits when they
  are equal), realizing `|100⟩ ↔ |111⟩`. (Note this is **not** a controlled-SWAP of the last two
  qubits: a Fredkin gate would swap `|101⟩ ↔ |110⟩` and fix `|100⟩, |111⟩`.)
-/

namespace AxQM.Concrete

open Matrix

/-- **The signal populations of `ρ` (N&C 7.162)**: `(6, 2, 2, -2, 2, -2, -2, -6)` on the big-endian
three-spin basis `|000⟩, …, |111⟩`. Entry `i` equals `6 - 4·(Hamming weight of i)`. -/
def logicalLabelDiag : Fin 8 → ℂ := ![6, 2, 2, -2, 2, -2, -2, -6]

/-- **The signal populations of `ρ'` after logical labeling (N&C 7.164)**:
`(6, -2, -2, -2, -6, 2, 2, 2)`. -/
def logicalLabelDiag' : Fin 8 → ℂ := ![6, -2, -2, -2, -6, 2, 2, 2]

/-- **`ρ` of N&C (7.162)**: the three-spin deviation density matrix `δ I + α · diag(populations)`,
with background `δ I` and signal `α · diag logicalLabelDiag`. -/
noncomputable def logicalLabelRho (δ α : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  δ • (1 : Matrix (Fin 8) (Fin 8) ℂ) + α • Matrix.diagonal logicalLabelDiag

/-- **`ρ'` of N&C (7.164)**: the state after the logical-labeling permutation,
`δ I + α · diag logicalLabelDiag'`. -/
noncomputable def logicalLabelRho' (δ α : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  δ • (1 : Matrix (Fin 8) (Fin 8) ℂ) + α • Matrix.diagonal logicalLabelDiag'

/-- **Gate `A₀₁` — a doubly-controlled `NOT` on the first qubit, active when the last two qubits are
`|01⟩`.** It flips `q₀` exactly on the control pattern `(q₁, q₂) = (0, 1)`, i.e. it is the basis
transposition `|001⟩ ↔ |101⟩` (indices `1 ↔ 5`) and fixes every other computational basis state. -/
noncomputable def logicalLabelCCNot01 : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if Equiv.swap 1 5 i = j then 1 else 0

/-- **Gate `A₁₀` — a doubly-controlled `NOT` on the first qubit, active when the last two qubits are
`|10⟩`.** It flips `q₀` exactly on the control pattern `(q₁, q₂) = (1, 0)`, i.e. the basis
transposition `|010⟩ ↔ |110⟩` (indices `2 ↔ 6`), fixing every other computational basis state. -/
noncomputable def logicalLabelCCNot10 : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if Equiv.swap 2 6 i = j then 1 else 0

/-- **Gate `B` — controlled (on `q₀ = |1⟩`) exchange `|00⟩ ↔ |11⟩` of the last two qubits.** When
the first qubit is `|1⟩` it flips *both* last qubits whenever they are equal (`|00⟩ ↔ |11⟩`, fixing
`|01⟩, |10⟩`); when `q₀ = |0⟩` it acts trivially. As a basis permutation this is the transposition
`|100⟩ ↔ |111⟩` (indices `4 ↔ 7`). This is **not** a controlled-`SWAP` (Fredkin) of the last two
qubits — a Fredkin would instead exchange `|101⟩ ↔ |110⟩` and fix `|100⟩, |111⟩`. -/
noncomputable def logicalLabelCFlip : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if Equiv.swap 4 7 i = j then 1 else 0

/-- **The logical-labeling circuit `P`** (Exercise 7.43) as the explicit product of its three gates:
the two doubly-controlled-`NOT`s `logicalLabelCCNot01`, `logicalLabelCCNot10` and the controlled
exchange `logicalLabelCFlip` (written right-to-left, so the leftmost factor acts last). -/
noncomputable def logicalLabelCircuit : Matrix (Fin 8) (Fin 8) ℂ :=
  logicalLabelCFlip * logicalLabelCCNot10 * logicalLabelCCNot01

/-- **The circuit `P` is unitary** — a genuine quantum operation. -/
theorem logicalLabelCircuit_mem_unitaryGroup :
    logicalLabelCircuit ∈ Matrix.unitaryGroup (Fin 8) ℂ := sorry

/-- **Exercise 7.43 (N&C 7.164)**: the logical-labeling circuit `P` transforms `ρ` into `ρ'`,
`P ρ P† = ρ'`. -/
theorem logicalLabelCircuit_conj_logicalLabelRho (δ α : ℂ) :
    logicalLabelCircuit * logicalLabelRho δ α * logicalLabelCircuitᴴ = logicalLabelRho' δ α := sorry

end AxQM.Concrete
