/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.PauliYGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.RelativePhase

/-!
# The Bell-basis measurement circuit (Nielsen & Chuang, Exercise 4.33)

N&C's circuit model measures only in the computational basis; to measure in another basis one first
*unitarily transforms that basis to the computational basis, then measures*.  For the Bell basis the
transforming circuit is a `CNOT` (control = first qubit, target = second) followed by a Hadamard on
the first qubit.  This file builds that circuit, proves it rotates the Bell basis onto the
computational basis (and its inverse prepares the Bell states), and derives Exercise 4.33's operator
answer: the induced measurement is the Bell-basis measurement `bellMeasurement`, whose measurement
operators and POVM elements are the four projectors onto the Bell states.

## Main definitions

* `bellMeasurementCircuit` — `(H ⊗ 1) ∘ CNOT`, the exercise's **measurement** circuit
  `|β_xy⟩ ↦ |xy⟩`.

## Main results

* `bellMeasurement_op_eq_bellMeasurementCircuit_conj` — **the measurement operators**: the induced
  measurement operator is `U† |xy⟩⟨xy| U = bellMeasurement.op (x, y) = |β_xy⟩⟨β_xy|`.
-/

open AxQM

namespace AxQM

noncomputable section

/-- **Bell-basis measurement circuit** `(H ⊗ 1) ∘ CNOT` (Nielsen & Chuang Exercise 4.33). It rotates
the Bell basis onto the computational basis, so measuring it in the computational basis realises a
measurement in the Bell basis. -/
def bellMeasurementCircuit : Evolution (qubit ⊗ qubit) :=
  (hadamardGate.onLeft qubit).comp cnotGate

/-- **The measurement operators (Nielsen & Chuang Exercise 4.33).**  Running the circuit `U` and
then measuring in the computational basis induces, for outcome `(x, y)`, the measurement
operator `U† |xy⟩⟨xy| U`; here written as the equal rank-one projector `|U†xy⟩⟨U†xy|` onto `U†
|xy⟩`. So the CNOT+H circuit realises the Bell-basis measurement, with the four Bell projectors
as its measurement operators. -/
theorem bellMeasurement_op_eq_bellMeasurementCircuit_conj (x y : Fin 2) :
    bellMeasurement.op (x, y)
      = ((InnerProductSpace.rankOne ℂ ((ContinuousLinearMap.adjoint bellMeasurementCircuit.op)
            ((qubitBasis x).vec ⊗ₜ[ℂ] (qubitBasis y).vec)))
          ((ContinuousLinearMap.adjoint bellMeasurementCircuit.op)
            ((qubitBasis x).vec ⊗ₜ[ℂ] (qubitBasis y).vec))) := sorry

end

end AxQM
