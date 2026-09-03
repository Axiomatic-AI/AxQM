/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate

/-!
# AxQM — the Toffoli ancilla (magic) state (N&C Exercises 10.68, 10.72)

The entangled three-qubit *ancilla state* at the heart of Nielsen & Chuang's fault-tolerant Toffoli
construction (Exercise 10.68, the leftmost dotted box of the Figure on p. 488; the state prepared in
Exercise 10.72).

## Main declarations
* `toffoliAncillaPrep` — the preparation `Evolution` `C²(X) · H₁ · H₂` on the three-qubit register
  (Hadamards on the two control wires, then the Toffoli).
* `toffoliAncilla` — the ancilla state, defined as the output `toffoliAncillaPrep |000⟩` of that
  circuit (a genuine `PureState`, no normalization side-condition, since `Evolution`s are unitary).
* `toffoliAncilla_vec` — **the value of the ancilla state:**
  `|Θ_T⟩ = ½ (|000⟩ + |010⟩ + |100⟩ + |111⟩)` (N&C eq. of Exercise 10.72), the explicit
  computational-basis expansion.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The Toffoli ancilla preparation circuit** (Nielsen & Chuang, Exercise 10.68 part (2), leftmost
dotted box; Exercise 10.72): a Hadamard on each of the two control qubits, then a Toffoli gate, on
the three-qubit register `qubit ⊗ (qubit ⊗ qubit)`. Applied to `|000⟩` it prepares the entangled
ancilla `toffoliAncilla`. -/
def toffoliAncillaPrep : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  toffoliGate.comp
    ((hadamardGate.onLeft (qubit ⊗ qubit)).comp ((hadamardGate.onLeft qubit).onRight qubit))

/-- **The Toffoli ancilla (magic) state** `|Θ_T⟩ = ½(|000⟩ + |010⟩ + |100⟩ + |111⟩)`, defined as the
output `C²(X)·H₁·H₂ |000⟩` of the preparation circuit `toffoliAncillaPrep`. This is the resource
state consumed by the fault-tolerant Toffoli circuit and the state prepared in Exercise 10.72. -/
def toffoliAncilla : PureState (qubit ⊗ (qubit ⊗ qubit)) :=
  toffoliAncillaPrep.evolvePure (qubitThreeBasis (0, 0, 0))

/-- **The value of the Toffoli ancilla state** (Nielsen & Chuang, Exercise 10.72; the ancilla of
Exercise 10.68 part (2)):

  `|Θ_T⟩ = ½ (|000⟩ + |010⟩ + |100⟩ + |111⟩)`. -/
theorem toffoliAncilla_vec :
    toffoliAncilla.vec
      = (2⁻¹ : ℂ) • ((qubitThreeBasis (0, 0, 0)).vec + (qubitThreeBasis (0, 1, 0)).vec
          + (qubitThreeBasis (1, 0, 0)).vec + (qubitThreeBasis (1, 1, 1)).vec) := sorry

end AxQM
