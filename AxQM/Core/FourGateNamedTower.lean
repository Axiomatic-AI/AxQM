/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.FourGateReachableWire
import AxQM.Basic.API.QuditGate
import AxQM.Concrete.RotationDecompositionXY
import AxQM.ToMathlib.NumberTheory.CosThreeFifthsIrrational
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import AxQM.Basic.API.FourGateReversibleWire
import AxQM.Concrete.ControlledSingleQubit
import AxQM.Concrete.QFTTwoLevel
import Mathlib.LinearAlgebra.Matrix.Swap
import AxQM.Concrete.TwoLevelEmbedding
import AxQM.Concrete.MultiControlledSingleQubit
import AxQM.Concrete.ABCDecomposition
import AxQM.Concrete.PermutationGate
import AxQM.Concrete.MultiControlledNot
import AxQM.Concrete.Pauli
import AxQM.Concrete.MultiControlledNotCircuit
import AxQM.Concrete.ComplexExpUnit
import AxQM.Concrete.SingleQubitWire
import AxQM.Basic.API.HadamardGate
import AxQM.Concrete.QftGateCircuit
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle
import AxQM.Core.QtowerSingleWireGate
import AxQM.Core.QftRegisterBridge
import AxQM.Core.MultiControlledNotBasis
import AxQM.Core.QtowerTensorPow
import AxQM.Basic.API.WirePermutation
import AxQM.Basic.API.Qubit
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.ControlledRotation
import AxQM.Basic.API.HadamardRotation
import AxQM.Basic.API.AxisAngleGateValues
import AxQM.Core.McNotCircuitEvolution
import Mathlib.Topology.Instances.Matrix
import AxQM.Core.PlacedMultiControlledX
import AxQM.Basic.API.ControlledControlledUnitary

/-!
# The named four-gate tower submonoid, containing every reachable tower circuit
(N&C Exercise 4.43, four-gate bridge — the final named-gate assembly)

## Main declarations
* `namedMcNotGate k` — the **named `≤ 2`-control reversible gate**: `NOT = H·S²·H` (`k = 0`),
  `cnotGate` (`k = 1`), `toffoliGate` (`k = 2`), and the raw `mcCtrl (k) pauliXGate` filler for the
  unused `k ≥ 3`. The `k = 0` value is the `{H, S}` circuit `H·S²·H` (not a bare `pauliXGate`), so
  the generating set below names *exactly* the four gates `H, S, CNOT, Toffoli` — no spurious fifth
  primitive `X`.
* `namedReversibleTowerGenerators n` — the named reversible gates `namedMcNotGate k` (`k ≤ 2`)
  placed on an arbitrary wire set and transported onto the tower.
-/

namespace AxQM

noncomputable section

/-- **The named `≤ 2`-control reversible gate.** The multiply-controlled `NOT` with `k` controls,
for the reachable range `k ≤ 2`, as one of the named gates: `NOT = H·S²·H` (`k = 0`), the named
CNOT `cnotGate` (`k = 1`), the named Toffoli `toffoliGate` (`k = 2`); for the unused `k ≥ 3` it
is the raw `mcCtrl k pauliXGate` (a filler, never referenced by the reachable generators). -/
def namedMcNotGate : (k : ℕ) → Evolution (qtower k qubit)
  | 0 => hadamardGate.comp ((sGate.comp sGate).comp hadamardGate)
  | 1 => cnotGate
  | 2 => toffoliGate
  | (k + 3) => mcCtrl (k + 3) pauliXGate

/-- **The named `≤ 2`-control reversible tower generators.** -/
def namedReversibleTowerGenerators (n : ℕ) : Set (Evolution (qtower n qubit)) :=
  {E | ∃ (k b : ℕ) (_ : k ≤ 2) (σ : Equiv.Perm (Fin (k + 1 + b))) (h : k + 1 + b = n + 1),
      E = Evolution.congr (qtowerQubitTensorPow n).symm
            (((Evolution.congr (qtowerQubitTensorPow k) (namedMcNotGate k)).onWires b σ).congr
              (QSystem.tensorPowCongr qubit (finCongr h)))}

end

end AxQM
