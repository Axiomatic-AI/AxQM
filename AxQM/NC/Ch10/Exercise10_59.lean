/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.Associator
import AxQM.Basic.API.SystemIsoComm
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.Basic.API.Fredkin
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.ControlledUnitary
import AxQM.NC.Ch4.Exercise4_17

/-!
# Nielsen & Chuang, Exercise 10.59 (Simplifying the Steane syndrome circuit)

*(N&C p. 474.)*

Using Figs 10.14/10.15 identities, replace syndrome circuit Fig 10.16 with Fig 10.17.

* `measureObservableCircuit_zTypeGenerator_eq_fig1017Block` — a `Z`-type generator `Z₁Z₂` compiles
  to two bare reversed CNOTs (no Hadamards).
* `measureObservableCircuit_xTypeGenerator_eq_fig1017Block` — an `X`-type generator `X₁X₂` compiles
  to Hadamard-conjugated reversed CNOTs (the `H • H •` rows).
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-! ### The per-generator syndrome-block replacement (Figure 10.16 → Figure 10.17)

A Figure-10.16 ancilla block Hadamard-controls a *product* of single-wire Paulis — a stabilizer
generator `gₐ = ∏ᵢ Pᵢ`; the block equals the Figure-10.17 block, a *sequence* of one-Pauli blocks
with the ancilla Hadamards gone. -/

/-- **Nielsen & Chuang, Figure 10.16 → 10.17 — a `Z`-type generator.** The Figure-10.16 syndrome
block for a two-qubit `Z`-type stabilizer generator `Z₁Z₂` — one ancilla Hadamard-controlling
the product `(Z ⊗ 1)·(1 ⊗ Z) = Z ⊗ Z` — equals the Figure-10.17 block. -/
theorem measureObservableCircuit_zTypeGenerator_eq_fig1017Block :
    measureObservableCircuit ((pauliZGate.onLeft qubit).comp (pauliZGate.onRight qubit))
      = (Evolution.congr (QSystem.assoc qubit qubit qubit).symm
            (reversedCnotGate.onLeft qubit)).comp
          (Evolution.congr (QSystem.Iso.leftComm qubit qubit qubit)
            (reversedCnotGate.onRight qubit)) := sorry

/-- **Nielsen & Chuang, Figure 10.16 → 10.17 — an `X`-type generator.** The Figure-10.16 syndrome
block for a two-qubit `X`-type stabilizer generator `X₁X₂` — one ancilla Hadamard-controlling
`(X ⊗ 1)·(1 ⊗ X) = X ⊗ X` — equals the Figure-10.17 block: on each data wire a **reversed CNOT**
into the ancilla conjugated by Hadamards on that wire (the `H • H •` pattern of the `X` rows of
Figure 10.17), with the ancilla Hadamards gone. -/
theorem measureObservableCircuit_xTypeGenerator_eq_fig1017Block :
    measureObservableCircuit ((pauliXGate.onLeft qubit).comp (pauliXGate.onRight qubit))
      = (Evolution.congr (QSystem.assoc qubit qubit qubit).symm
            (((hadamardGate.onRight qubit).comp
              (reversedCnotGate.comp (hadamardGate.onRight qubit))).onLeft qubit)).comp
          (Evolution.congr (QSystem.Iso.leftComm qubit qubit qubit)
            (((hadamardGate.onRight qubit).comp
              (reversedCnotGate.comp (hadamardGate.onRight qubit))).onRight qubit)) := sorry

end AxQM
