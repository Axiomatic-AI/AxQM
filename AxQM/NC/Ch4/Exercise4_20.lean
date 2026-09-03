/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.NC.Ch2.Exercise2_52

/-!
# Nielsen & Chuang, Exercise 4.20 (CNOT basis transformations)

*(N&C p. 179.)*

Show CNOT conjugated by Hadamards swaps control/target; give ± basis action.

* `cnotGate_evolvePure_qubitPlus_qubitPlus` — eq. (4.24): `CNOT(|+⟩ ⊗ |+⟩) = |+⟩ ⊗ |+⟩`.
* `cnotGate_evolvePure_qubitMinus_qubitPlus` — eq. (4.25): `CNOT(|-⟩ ⊗ |+⟩) = |-⟩ ⊗ |+⟩`.
* `cnotGate_evolvePure_qubitPlus_qubitMinus` — eq. (4.26): `CNOT(|+⟩ ⊗ |-⟩) = |-⟩ ⊗ |-⟩`.
* `cnotGate_evolvePure_qubitMinus_qubitMinus` — eq. (4.27): `CNOT(|-⟩ ⊗ |-⟩) = |+⟩ ⊗ |-⟩`.
* `cnotGate_hadamardConj_evolvePure_qubitBasis` — the circuit identity (the "swaps control/target"
  statement): the Hadamard-conjugated CNOT `(H ⊗ H) · CNOT · (H ⊗ H)` sends the computational basis
  state `|c⟩ ⊗ |t⟩` to `|c ⊕ t⟩ ⊗ |t⟩` — the *reversed* CNOT truth table (control on the second
  qubit, target on the first), the sense in which conjugating by Hadamards interchanges control and
  target.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The `±`-basis action of `CNOT` (N&C eqs. 4.24–4.27) -/

/-- **N&C eq. (4.24):** `CNOT(|+⟩ ⊗ |+⟩) = |+⟩ ⊗ |+⟩`. -/
theorem cnotGate_evolvePure_qubitPlus_qubitPlus :
    cnotGate.evolvePure (qubitPlus ⊗ qubitPlus) = qubitPlus ⊗ qubitPlus := sorry

/-- **N&C eq. (4.25):** `CNOT(|-⟩ ⊗ |+⟩) = |-⟩ ⊗ |+⟩`. -/
theorem cnotGate_evolvePure_qubitMinus_qubitPlus :
    cnotGate.evolvePure (qubitMinus ⊗ qubitPlus) = qubitMinus ⊗ qubitPlus := sorry

/-- **N&C eq. (4.26):** `CNOT(|+⟩ ⊗ |-⟩) = |-⟩ ⊗ |-⟩`. -/
theorem cnotGate_evolvePure_qubitPlus_qubitMinus :
    cnotGate.evolvePure (qubitPlus ⊗ qubitMinus) = qubitMinus ⊗ qubitMinus := sorry

/-- **N&C eq. (4.27):** `CNOT(|-⟩ ⊗ |-⟩) = |+⟩ ⊗ |-⟩`. -/
theorem cnotGate_evolvePure_qubitMinus_qubitMinus :
    cnotGate.evolvePure (qubitMinus ⊗ qubitMinus) = qubitPlus ⊗ qubitMinus := sorry

/-! ### The unifying `X`-basis truth table and the reversed-CNOT circuit identity -/

/-- **The circuit identity `(H ⊗ H) · CNOT · (H ⊗ H) = CNOT_reversed` (N&C Exercise 4.20, Part 1),
as a reversed truth table.** Conjugating `CNOT` (control on the first qubit, target on the
second) by a Hadamard on each qubit sends the computational basis state `|c⟩ ⊗ |t⟩` to `|c ⊕ t⟩
⊗ |t⟩`: the *second* qubit `t` now plays the role of the control (unchanged, and XORed into the
first qubit), while the *first* qubit `c` is the target. Control and target have interchanged
roles.
-/
theorem cnotGate_hadamardConj_evolvePure_qubitBasis (c t : Fin 2) :
    ((hadamardGate ⊗ hadamardGate).comp
          (cnotGate.comp (hadamardGate ⊗ hadamardGate))).evolvePure
        ((qubitBasis c) ⊗ (qubitBasis t))
      = (qubitBasis (c + t)) ⊗ (qubitBasis t) := sorry

end AxQM
