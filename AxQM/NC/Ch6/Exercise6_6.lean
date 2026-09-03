/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ConditionalPhaseShift
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.NC.Ch4.Exercise4_17

/-!
# Nielsen & Chuang, Exercise 6.6 (the dotted-box conditional phase shift)

*(N&C p. 255.)*

Verify the gates in the dotted box perform conditional phase shift 2|00><00| - I up to global phase.

* `dottedBoxCircuit` — the dotted box as a closed-system `Evolution` on `qubit ⊗ qubit`, the exact
  gate list `(X ⊗ X) · (1 ⊗ H) · CNOT · (1 ⊗ H) · (X ⊗ X)`.
* `dottedBoxCircuit_evolve_eq_conditionalPhaseShift` — the exercise, up to global phase: for every
  state `ρ`, the box and the conditional phase shift `2|00⟩⟨00| − I`
  (`conditionalPhaseShiftZeroZero`) induce the *same* evolution, `dottedBoxCircuit.evolve ρ =
  conditionalPhaseShiftZeroZero.evolve ρ`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The dotted box of Box 6.1** as a closed-system `Evolution` on the two query qubits: the exact
gate list `(X ⊗ X) · (1 ⊗ H) · CNOT · (1 ⊗ H) · (X ⊗ X)`, reading the figure left to right (the
right-most factor `X ⊗ X` is applied first). Here `X ⊗ X = pauliXGate ⊗ pauliXGate`, `1 ⊗ H =
hadamardGate.onRight qubit`, and `CNOT = cnotGate`. -/
def dottedBoxCircuit : Evolution (qubit ⊗ qubit) :=
  (pauliXGate ⊗ pauliXGate).comp
    ((hadamardGate.onRight qubit).comp
      (cnotGate.comp
        ((hadamardGate.onRight qubit).comp
          (pauliXGate ⊗ pauliXGate))))

/-- **Nielsen & Chuang, Exercise 6.6.** The gates in the dotted box perform the conditional phase
shift `2|00⟩⟨00| − I`, up to an unimportant global phase: for every state `ρ`, the box and the
conditional phase shift induce the same evolution, `dottedBoxCircuit.evolve ρ =
conditionalPhaseShiftZeroZero.evolve ρ`. The two unitaries are `I − 2|00⟩⟨00|` and its negation
`2|00⟩⟨00| − I`, i.e. their operators differ by the unit-modulus scalar `c = −1`, which cancels
in the conjugation `U ρ U†` — which is exactly why the phase is physically unimportant. -/
theorem dottedBoxCircuit_evolve_eq_conditionalPhaseShift (ρ : State (qubit ⊗ qubit)) :
    dottedBoxCircuit.evolve ρ = conditionalPhaseShiftZeroZero.evolve ρ := sorry

end AxQM
