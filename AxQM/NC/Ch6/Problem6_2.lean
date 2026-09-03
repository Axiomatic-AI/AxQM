/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PureState
import AxQM.Basic.API.Reflection
import AxQM.Basic.API.Qubit
import AxQM.ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.PauliYGate
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition

/-!
# Nielsen & Chuang, Problem 6.2 (generalized quantum searching)

*(N&C p. 274.)*

Generalized quantum searching: implement U_psi=I-2|psi><psi| from U; identify oracle among a set;
research k-state case.

* `reflectionEvolution_eq_conj_of_prep` — part (1).
* `searchReflectionOracle`, `oracleBellState`, `bellOutcome` — part (2b): the three oracles, the
  state each produces on a shared Bell pair, and the Bell-basis outcome it is identified by.
* `oracleBellState_bornProb` — `Pr[outcome β_{bellOutcome i} ∣ oracle j] = δᵢⱼ`, so
  one oracle application followed by one Bell measurement identifies the oracle.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **N&C Problem 6.2(1).** How to implement `U_ψ = I − 2|ψ⟩⟨ψ|` from a state-preparation circuit.

`U_ψ = U ∘ U_φ ∘ U†`.

Here `U_φ = reflectionEvolution |0⟩⊗ⁿ` is the conditional phase shift `I − 2|0⟩⊗ⁿ⟨0|⊗ⁿ`.
-/
theorem reflectionEvolution_eq_conj_of_prep {U : Evolution S} {φ ψ : PureState S}
    (h : U.evolvePure φ = ψ) :
    reflectionEvolution ψ = U.comp ((reflectionEvolution φ).comp U.adjoint) := sorry

/-! ## Part (2) — one-shot identification via a Bell measurement (superdense coding)

To identify the unknown oracle `O` with a single application, prepare a Bell pair `|Φ⁺⟩`, apply
`O` to its **first** qubit, and measure both qubits in the Bell basis.  This is the
superdense-coding protocol run in reverse (N&C §2.3). -/

/-- The three oracles of Problem 6.2(2): the reflection oracles `U_|ψᵢ⟩ = I − 2|ψᵢ⟩⟨ψᵢ|` for
`|ψ₁⟩ = |1⟩`, `|ψ₂⟩ = |−⟩`, `|ψ₃⟩ = |−i⟩`. -/
def searchReflectionOracle : Fin 3 → Evolution qubit
  | 0 => reflectionEvolution (qubitBasis 1)
  | 1 => reflectionEvolution qubitMinus
  | 2 => reflectionEvolution qubitMinusI

/-- The two-qubit state after applying oracle `i` to Alice's (left) half of the shared Bell pair
`|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. -/
def oracleBellState (i : Fin 3) : PureState (qubit ⊗ qubit) :=
  ((searchReflectionOracle i).onLeft qubit).evolvePure bellPhiPlus

/-- The Bell-basis outcome each oracle deterministically produces: `Z ↦ β₁₀`, `X ↦ β₀₁`,
`Y ↦ β₁₁`. -/
def bellOutcome : Fin 3 → Fin 2 × Fin 2
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)

/-- **N&C Problem 6.2(2) — the discrimination.**  Preparing `|Φ⁺⟩`, applying the unknown oracle
`O = searchReflectionOracle j` to its first qubit and measuring in the Bell basis returns outcome
`bellOutcome i` with probability `1` when `i = j` and `0` otherwise:

`Pr[outcome β_{bellOutcome i} ∣ (O_j ⊗ I)|Φ⁺⟩] = δᵢⱼ`.

Since the three oracles yield three distinct *deterministic* outcomes, one oracle application
followed by one Bell measurement identifies the oracle — the superdense-coding solution. -/
theorem oracleBellState_bornProb (i j : Fin 3) :
    bellMeasurement.bornProb ((oracleBellState j).toState) (bellOutcome i)
      = if i = j then 1 else 0 := sorry

end AxQM
