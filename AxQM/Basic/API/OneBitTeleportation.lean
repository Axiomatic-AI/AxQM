/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.Fredkin
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.ControlMeasurementCommute
import AxQM.Basic.API.MeasurementOperation

/-!
# AxQM — the measured-swap circuit branch decompositions

The core of Nielsen & Chuang **Exercise 10.65**: replacing a controlled-`NOT` in a
qubit swap by a *measurement* and a *classically-controlled single-qubit correction*.  N&C's two
alternative circuits, applied to an unknown input `|ψ⟩ ⊗ |0⟩`, produce — *before* the
measurement — a state of the two-branch form
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The first measured-swap circuit** of N&C Exercise 10.65: a `CNOT` (control = qubit 1) followed
by a Hadamard on qubit 1, `(H ⊗ 1) · CNOT`.  Feeding `|ψ⟩ ⊗ |0⟩` and measuring qubit 1 leaves qubit
2 in `Z^m|ψ⟩` (`m` the outcome), undone by a classically-controlled `Z`. -/
def measuredSwapCircuit1 : Evolution (qubit ⊗ qubit) :=
  (hadamardGate.onLeft qubit).comp cnotGate

/-- **The second measured-swap circuit** of N&C Exercise 10.65: a Hadamard on qubit 2 followed by
the reversed `CNOT` (control = qubit 2), `reversedCNOT · (1 ⊗ H)`.  Feeding `|ψ⟩ ⊗ |0⟩` and
measuring qubit 1 leaves qubit 2 in `X^m|ψ⟩`, undone by a classically-controlled `X`. -/
def measuredSwapCircuit2 : Evolution (qubit ⊗ qubit) :=
  reversedCnotGate.comp (hadamardGate.onRight qubit)

end AxQM
