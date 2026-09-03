/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliStringExpCircuit
import AxQM.Basic.API.PauliDiagWire
import AxQM.Core.CircuitBudget
import AxQM.Basic.API.TensorPowSplit
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.Associator
import AxQM.Basic.API.LeftPairGate
import AxQM.Core.QtowerSingleWireGate
import AxQM.Basic.API.MeasureObservable
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.Basic.API.MutualInformation
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.Evolution
import AxQM.Basic.Composite
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.SystemIso
import AxQM.Basic.API.QuditGate
import AxQM.Basic.API.HadamardGate
import AxQM.Concrete.QftGateCircuit
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle
import AxQM.Core.QftRegisterBridge
import AxQM.Core.MultiControlledNotBasis
import AxQM.Core.QtowerTensorPow
import AxQM.Basic.API.WirePermutation
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import AxQM.Basic.API.Qudit
import AxQM.Concrete.MultiControlledSingleQubit
import AxQM.Concrete.ABCDecomposition
import AxQM.Concrete.PermutationGate
import AxQM.Concrete.ControlledSingleQubit
import AxQM.Concrete.MultiControlledNot
import AxQM.Concrete.Pauli
import AxQM.Concrete.MultiControlledNotCircuit
import AxQM.Concrete.ComplexExpUnit
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.CnotFanEvolution
import AxQM.Basic.API.FourGateReversibleWire
import AxQM.Core.McNotCircuitEvolution
import AxQM.Basic.API.FourGateReachableWire
import AxQM.Basic.API.ControlledUnitary

/-!
# Problem 4.3(3) gate count: the assembled Figure-4.19 circuit is `O(n)` elementary gates

Problem 4.3(3) asks to implement the Trotter summand `exp(-i h_g g Δ)` — a rotation about the Pauli
string `g` — using `O(n)` one- and two-qubit gates. This file gives the assembled
compute–rotate–uncompute cascade `B ∘ V† ∘ R_z ∘ V ∘ B†` (`pauliStringExpCircuit`) a genuine
`CircuitBudget` — the **elementary-gate count** half of Problem 4.3(3).
-/

namespace AxQM

noncomputable section

/-- **Problem 4.3(3): the Figure-4.19 circuit implementing `exp(-i h_g g Δ)` costs `O(n)` gates.**
For a collector wire `c ∉ ts` on the `(n+1)`-qubit register, the assembled
compute–rotate–uncompute cascade `pauliStringExpCircuit (n+1) g c ts θ = B · V† · R_z · V · B†`
has budget

`CircuitBudget (pauliStringExpCircuit (n+1) g c ts θ) (2 * ts.length) (2 * n + 3)`:

at most `2 · ts.length` two-qubit (`≤ 2`-control) gates and `2n + 3` single-qubit gates. When
`g`'s support is `insert c ts`, `ts.length = |support| − 1 ≤ n`, so this is the linear — `O(n)` —
one- and two-qubit gate count Problem 4.3(3) demands.

The budget is independent of the correctness hypotheses.
-/
theorem pauliStringExpCircuit_circuitBudget {n : ℕ} (g : Fin (n + 1) → Fin 4) (c : Fin (n + 1))
    (ts : List (Fin (n + 1))) (hc : c ∉ ts) (θ : ℝ) :
    CircuitBudget (pauliStringExpCircuit (n + 1) g c ts θ) (2 * ts.length) (2 * n + 3) := sorry

end

end AxQM
