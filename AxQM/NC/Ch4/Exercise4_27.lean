/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.LeftPairGate
import AxQM.Concrete.PartialCyclicPermutation

/-!
# Nielsen & Chuang, Exercise 4.27 (partial cyclic permutation from CNOTs and Toffoli gates)

*(N&C p. 183.)*

Using CNOTs and Toffoli gates, build a circuit for a partial cyclic permutation.

* `partialCyclicPermCircuit` — the circuit: an eight-gate composition of `CNOT`s and Toffoli gates
  on `qubit ⊗ (qubit ⊗ qubit)`.
* `partialCyclicPermCircuit_evolvePure_qubitBasis` — the circuit performs the transformation
  (4.31), `circuit|q₁,q₂,q₃⟩ = |partialCyclicShift q₁ q₂ q₃⟩` for every computational basis state.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

open Concrete (partialCyclicShift)

/-- **The Exercise 4.27 circuit.** A composition of eight `CNOT` and Toffoli gates on
`qubit ⊗ (qubit ⊗ qubit)` implementing the partial cyclic permutation (4.31). In application order
(innermost first): `CNOT₁→₂`, `CNOT₂→₁`, `Toffoli₁,₃→₂`, `CNOT₂→₁`, `CNOT₃→₂`, `Toffoli₁,₂→₃`,
`CNOT₁→₂`, `CNOT₂→₃`. -/
def partialCyclicPermCircuit : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (cnotGate.onRight qubit).comp
    (cnotLeftGate.comp
      (toffoliGate.comp
        ((reversedCnotGate.onRight qubit).comp
          (reversedCnotLeftGate.comp
            (middleToffoliGate.comp
              (reversedCnotLeftGate.comp cnotLeftGate))))))

/-- **Nielsen & Chuang Exercise 4.27.** The circuit `partialCyclicPermCircuit`, built from `CNOT`
and Toffoli gates alone, performs the transformation (4.31): on every computational basis state
`|q₁, q₂, q₃⟩` it acts as the partial cyclic permutation `partialCyclicShift`, fixing `|000⟩`
and cyclically shifting the seven non-zero basis states. This equality of the circuit's action
with the permutation matrix (4.31) is the content of the exercise. -/
theorem partialCyclicPermCircuit_evolvePure_qubitBasis (q1 q2 q3 : Fin 2) :
    partialCyclicPermCircuit.evolvePure ((qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)))
      = (qubitBasis (partialCyclicShift q1 q2 q3).1)
          ⊗ ((qubitBasis (partialCyclicShift q1 q2 q3).2.1)
              ⊗ (qubitBasis (partialCyclicShift q1 q2 q3).2.2)) := sorry

end AxQM
