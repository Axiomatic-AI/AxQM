/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Composite
import AxQM.Basic.API.Qudit
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.QuditGate
import AxQM.Basic.API.HadamardGate
import AxQM.Concrete.QftGateCircuit
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle
import AxQM.Concrete.MultiControlledSingleQubit
import AxQM.Concrete.ABCDecomposition
import AxQM.Concrete.PermutationGate
import AxQM.Concrete.ControlledSingleQubit
import AxQM.Concrete.MultiControlledNot
import AxQM.Concrete.Pauli
import AxQM.Concrete.MultiControlledNotCircuit
import AxQM.Concrete.ComplexExpUnit
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
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.SystemIso
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Core.QftRegisterBridge
import AxQM.Core.MultiControlledNotBasis
import AxQM.Core.QtowerTensorPow
import AxQM.Basic.API.WirePermutation
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import AxQM.Core.MultiControlledReduction
import AxQM.Basic.API.ControlledUnitary

/-!
# Nielsen & Chuang, Problem 4.1 (Computable phase shifts)

*(N&C p. 212.)*

Build a circuit with 2T+n gates implementing |x> -> exp(-2pi i f(x)/2^n)|x>.

* `computablePhaseAngle`
* `computablePhaseShiftCircuit`
* `computablePhaseShiftCircuit_hasEigenstate` — correctness (eq. 4.116): for an oracle `Uf`
  computing `|x⟩|0⟩ ↦ |x⟩|f(x)⟩`, every input `|x⟩|0⟩` is an eigenstate of `C` with eigenvalue
  `exp(−2πi f(x)/2ⁿ)`.
* `computablePhaseShiftCircuit_circuitBudget` — the full `2T + n` gate count (eq. 4.116):
  for an oracle with `CircuitBudget Uf T 0`, the whole circuit `C = U_f† ∘ (I_A ⊗ D) ∘
  U_f` has `CircuitBudget C (2T) (n+1)` — at most `2T` `≤ 2`-control gates and `n+1` single-qubit
  gates.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- The **computable phase angle** `θ_k = −2π k / 2ⁿ` of Nielsen & Chuang Problem 4.1, for an
ancilla index `k : Fin (2ⁿ)`. It is chosen so that `exp(i · θ_k) = exp(−2πi k / 2ⁿ)` is the phase
(eq. 4.116) that the circuit imprints when the ancilla holds `|k⟩`. -/
def computablePhaseAngle (n : ℕ) (k : Fin (2 ^ n)) : ℝ := -(2 * Real.pi * (k : ℝ)) / (2 ^ n : ℝ)

/-- The **computable-phase-shift circuit** `C = U_f† ∘ (I_A ⊗ D) ∘ U_f` of Nielsen & Chuang Problem
4.1, built from a reversible oracle `Uf` on the input⊗ancilla register `qudit (2^m) ⊗ qudit
(2^n)`. Here `D = diagPhase (computablePhaseAngle n)` is the ancilla phase gate `|y⟩ ↦ exp(−2πi
y/2ⁿ)|y⟩`, `I_A ⊗ D = Evolution.id ⊗ D` acts as `D` on the ancilla only, and `U_f†`
(`Evolution.adjoint`) uncomputes the ancilla. -/
def computablePhaseShiftCircuit {m n : ℕ}
    (Uf : Evolution (qudit (2 ^ m) ⊗ qudit (2 ^ n))) :
    Evolution (qudit (2 ^ m) ⊗ qudit (2 ^ n)) :=
  Uf.adjoint.comp
    (((Evolution.id (S := qudit (2 ^ m))).tmul (diagPhase (computablePhaseAngle n))).comp Uf)

/-- **Computable phase shifts** (Nielsen & Chuang Problem 4.1, eq. 4.116). Let `Uf` be a reversible
oracle on the register `qudit (2^m) ⊗ qudit (2^n)` computing `|x⟩|0⟩ ↦ |x⟩|f(x)⟩` for every
input `x` (the `y = 0` instance of the Toffoli-implemented map `(x,y) ↦ (x, y ⊕ f(x))`). Then,
for each `x`, the initialized state `|x⟩|0⟩` is an **eigenstate** of the circuit `C = U_f† ∘
(I_A ⊗ D) ∘ U_f` with eigenvalue `exp(−2πi f(x)/2ⁿ)`:

`C |x⟩|0⟩ = exp(−2πi f(x)/2ⁿ) · |x⟩|0⟩`.

Thus `C` implements the unitary `|x⟩ ↦ exp(−2πi f(x)/2ⁿ)|x⟩` on the input register, returning
the ancilla to `|0⟩`.
-/
theorem computablePhaseShiftCircuit_hasEigenstate {m n : ℕ}
    (Uf : Evolution (qudit (2 ^ m) ⊗ qudit (2 ^ n)))
    (f : Fin (2 ^ m) → Fin (2 ^ n))
    (hUf : ∀ x : Fin (2 ^ m), Uf.evolvePure ((quditBasis x).tmul (quditBasis 0))
        = (quditBasis x).tmul (quditBasis (f x)))
    (x : Fin (2 ^ m)) :
    (computablePhaseShiftCircuit Uf).HasEigenstate
      (Complex.exp ((computablePhaseAngle n (f x) : ℂ) * Complex.I))
      ((quditBasis x).tmul (quditBasis 0)) := sorry

/-- **The `2T + n` gate count** (Nielsen & Chuang Problem 4.1).
For an `(m+1)`-qubit input register `A = qudit (2^(m+1))`, an `(n+1)`-qubit ancilla
`B = qudit (2^(n+1))`, and a reversible oracle `Uf` on `A ⊗ B` costing `T` `≤ 2`-control gates
(Toffoli/CNOT/NOT) and **no** single-qubit gates (`CircuitBudget Uf T 0` — the exercise's own given,
"`f` computable reversibly using `T` Toffoli gates"), the computable-phase-shift circuit
`C = U_f† ∘ (I_A ⊗ D) ∘ U_f` has elementary-gate budget

`CircuitBudget (computablePhaseShiftCircuit Uf) (2 * T) (n + 1)`:

at most `2T` `≤ 2`-control gates and at most `n+1` single-qubit gates — the exercise's `2T + n`
count, with the ancilla's `n+1` qubits playing the role of N&C's positive integer `n`.
-/
theorem computablePhaseShiftCircuit_circuitBudget {m n : ℕ} (T : ℕ)
    (Uf : Evolution (qudit (2 ^ (m + 1)) ⊗ qudit (2 ^ (n + 1))))
    (hUf : CircuitBudget Uf T 0) :
    CircuitBudget (computablePhaseShiftCircuit Uf) (2 * T) (n + 1) := sorry

end AxQM
