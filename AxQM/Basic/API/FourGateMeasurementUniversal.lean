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
import AxQM.ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM
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
import AxQM.Basic.API.RzThreeFifthsMeasurement
import AxQM.Core.FourGateNamedTower

/-!
# `H, S, CNOT, Toffoli` with measurement are universal — the measurement→generator fusion
(N&C Exercise 4.43, four-gate bridge — the terminal)

Nielsen & Chuang **Exercise 4.43**: the four gates `H, S, CNOT, Toffoli`, together with
measurement, are universal for quantum computation.

## The fusion

* `IsFourGateMeasurementRealised G` — **the measurement-realisation predicate.** A single-qubit
  gate `G : Evolution qubit` is *realised by the four-gate measurement gadget* when the Figure-4.17
  circuit `rzThreeFifthsCircuit`, post-selected on the success outcome `(0, 0)` of the two-ancilla
  measurement `rzTwoAncillaMeasurement`, applies `G` to the target: its first conjunct is the
  circuit + measurement's success action (`… = rzThreeFifthsAmp 0 0 t • |0,0,t⟩` — this is what
  makes the four-gate circuit `rzThreeFifthsCircuit` and the Measurement primitive
  `rzTwoAncillaMeasurement` genuinely appear), and its second conjunct pins `G` to that success
  amplitude (`rzThreeFifthsAmp 0 0 t • |t⟩ = c • G.op |t⟩`, `‖c‖² = 5/8`) — so `G.op` is determined
  on the computational basis up to the global scalar `c`, i.e. `G = R_z(θ)` up to an (unobservable)
  global phase.
* `fourGateMeasurementReachable n` — **the four-gate + measurement tower model.** It is generated
  by the tower-wire placements of the four named *unitary* gates `hadamardGate, sGate` (with
  `cnotGate, toffoliGate` entering through the named reversible gates `namedMcNotGate`) together
  with the tower-wire placements of *every gate the four-gate measurement gadget realises*
  (`{G | IsFourGateMeasurementRealised G}`). No `rotZGate` appears as a free generator — every
  rotation in the model is present because it is measurement-realised.
* `hsCnotToffoli_measurement_universal` — **the terminal.** For any tower evolution
  `T : Evolution (qtower n qubit)`, some global phase `e^{iα}` makes `e^{iα} • T.op` lie in the
  closure of the operator image of `fourGateMeasurementReachable n`: the circuits built from the
  four gates `H, S, CNOT, Toffoli` **together with the measurement-realised rotation** are dense in
  the unitaries up to a global phase.
-/

namespace AxQM

noncomputable section

/-- **A single-qubit gate realised by the four-gate measurement gadget**. `G`
is *realised* when the Figure-4.17 circuit `rzThreeFifthsCircuit` (`H, S, Toffoli` on two ancillas +
target), followed by the two-ancilla measurement `rzTwoAncillaMeasurement` post-selected on the
success outcome `(0, 0)`, applies `G` to the target:

* the success (Kraus) operator sends the circuit output on `|0, 0, t⟩` to
  `rzThreeFifthsAmp 0 0 t • |0, 0, t⟩` (the circuit + measurement's success action), and
* that amplitude equals `c • G.op` on the target for a scalar `c` with `‖c‖² = 5/8` (the
  input-independent success probability), which pins `G.op` on the computational basis up to the
  global scalar `c` — so `G` is `R_z(rzThreeFifthsAngle)` up to a global phase.

This is what a generator's being "supplied by the four gates + measurement" means. -/
def IsFourGateMeasurementRealised (G : Evolution qubit) : Prop :=
  (∀ t : Fin 2,
      (rzTwoAncillaMeasurement.op (0, 0))
          (rzThreeFifthsCircuit.evolvePure
            ((qubitBasis 0).tmul ((qubitBasis 0).tmul (qubitBasis t)))).vec
        = rzThreeFifthsAmp 0 0 t •
            ((qubitBasis 0).tmul ((qubitBasis 0).tmul (qubitBasis t))).vec) ∧
    ∃ c : ℂ, ‖c‖ ^ 2 = 5 / 8 ∧ ∀ t : Fin 2,
      rzThreeFifthsAmp 0 0 t • (qubitBasis t).vec
        = c • G.op (qubitBasis t).vec

/-- **The four-gate + measurement tower model.** The submonoid of `Evolution (qtower n qubit)`
generated by

* the single-tower-wire placements `Evolution.qtowerSingleWire n i g` of the named *unitary* gates
  `g ∈ {hadamardGate, sGate}` together with *every* measurement-realised gate
  `g ∈ {G | IsFourGateMeasurementRealised G}`, over every wire `i`, and
* the shared named reversible tower generators `namedReversibleTowerGenerators n`
  — the named gates `namedMcNotGate k` (`k ≤ 2` — `NOT = H·S²·H`,
  `cnotGate`, `toffoliGate`) placed on a wire set and transported onto the tower.

No `rotZGate` is posited as a generator; every rotation in the model is present only because the
four-gate measurement gadget realises it. Its unitary generators are the four named gates
`hadamardGate, sGate, cnotGate, toffoliGate`. -/
def fourGateMeasurementReachable (n : ℕ) :
    Submonoid (Evolution (qtower n qubit)) :=
  Submonoid.closure
    ((⋃ i : Fin (n + 1),
        Evolution.qtowerSingleWire n i ''
          (insert hadamardGate (insert sGate {G | IsFourGateMeasurementRealised G}))) ∪
      namedReversibleTowerGenerators n)

/-- **`H, S, CNOT, Toffoli` with measurement are universal for quantum computation** (N&C Exercise
4.43). For *any* tower evolution `T : Evolution (qtower n qubit)`, some global phase `e^{iα}`
makes

`e^{iα} • T.op ∈ closure ((·.op) '' fourGateMeasurementReachable n)`.

This is Exercise 4.43's universality conclusion.
-/
theorem hsCnotToffoli_measurement_universal {n : ℕ} (T : Evolution (qtower n qubit)) :
    ∃ α : ℝ, Complex.exp ((α : ℂ) * Complex.I) • T.op ∈
      closure ((fun E : Evolution (qtower n qubit) => E.op) ''
        (fourGateMeasurementReachable n : Set (Evolution (qtower n qubit)))) := sorry

end

end AxQM
