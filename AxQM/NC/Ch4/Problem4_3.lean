/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.PauliTrotterStep
import AxQM.Basic.API.PauliTrotter
import AxQM.Basic.API.PauliTrotterExplicit
import AxQM.Basic.API.ApproxError
import AxQM.Basic.API.PauliTrotterSummand
import AxQM.Core.PauliStringExpCircuitBudget
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
import AxQM.Basic.Composite
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.SystemIso
import AxQM.Core.QftRegisterBridge
import AxQM.Basic.API.NMRControlledZ
import AxQM.Basic.API.QuditGate
import AxQM.Basic.API.HadamardGate
import AxQM.Concrete.QftGateCircuit
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle
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
import AxQM.Core.MultiControlledNotBasis
import AxQM.Core.QtowerTensorPow
import AxQM.Basic.API.WirePermutation
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import AxQM.ToMathlib.Analysis.CStarAlgebra.Unitary.Exp
import AxQM.ToMathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Nielsen & Chuang, Problem 4.3 (Alternate universality construction) — Part 1, Hermitian generator

*(N&C p. 212.)*

Alternate universality: expand H=i ln U in Pauli products; approximate U via Trotter.

* `exists_pauliString_trotter_circuit_gateCount`
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Problem 4.3(6): the literal `O(n·16ⁿ/ε)` gate count.** *Every* unitary
`U` on `n+1` qubits can be approximated to within any accuracy `ε > 0` by an explicit one- and
two-qubit circuit — the `k`-fold Pauli–Trotter step `(pauliTrotterStep (n+1) h (1/k))ᵏ` — whose
**total gate count is `O(n·16ⁿ/ε)`**:
`total ≤ trotterProductConst · 4π² · (4n+3) · 16ⁿ⁺¹ / ε + 4ⁿ⁺¹ · (4n+3)`.

This is N&C's `O(n·16ⁿ/ε)` for the register of `n+1` qubits (N&C's "`n` qubits" is our `n+1`).
-/
theorem Evolution.exists_pauliString_trotter_circuit_gateCount {n : ℕ}
    (U : Evolution (qudit (2 ^ (n + 1)))) :
    ∃ (h : (Fin (n + 1) → Fin 4) → ℝ), ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, 1 ≤ k ∧
      ((pauliTrotterStep (n + 1) h (k : ℝ)⁻¹) ^ k).gateError U ≤ ε ∧
      CircuitBudget ((pauliTrotterStep (n + 1) h (k : ℝ)⁻¹) ^ k)
        (k * (4 ^ (n + 1) * (2 * n))) (k * (4 ^ (n + 1) * (2 * n + 3))) ∧
      ((k * (4 ^ (n + 1) * (2 * n)) + k * (4 ^ (n + 1) * (2 * n + 3)) : ℕ) : ℝ)
        ≤ NormedSpace.trotterProductConst * (4 * Real.pi ^ 2) *
            ((4 * (n : ℝ) + 3) * 16 ^ (n + 1)) / ε
          + 4 ^ (n + 1) * (4 * (n : ℝ) + 3) := sorry

end AxQM
