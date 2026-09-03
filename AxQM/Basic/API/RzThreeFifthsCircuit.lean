/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.AxisAngleGateValues
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.PiEighthGate
import AxQM.Basic.API.HadamardRotation

/-!
# AxQM.Basic.API — the Figure 4.17 measurement-based `R_z(θ)` circuit

The operator-level form of Nielsen & Chuang's Exercise 4.41: a three-qubit circuit with two
ancilla (control) qubits and one target qubit that, conditioned on both ancillas being measured
`0`, applies the `z`-rotation `R_z(θ)` with `cos θ = 3/5` to the target — and applies `Z` to the
target on every other measurement outcome.

## The readings (this chunk)

* `rzThreeFifthsCircuit_success_eq_rotZ` — **on both ancillas measured `0`, the circuit applies
  `R_z(θ)`.** The success (Kraus) operator `M₀₀ : |t⟩ ↦ rzThreeFifthsAmp 0 0 t · |t⟩` equals
  `c · R_z(rzThreeFifthsAngle)` for a scalar `c` with `‖c‖² = 5/8`, where
  `cos rzThreeFifthsAngle = 3/5` (`rzThreeFifthsAngle_cos`). Since `R_z` is unitary, `‖c‖² = 5/8` is
  the (input-independent) probability of the `00` outcome — Nielsen & Chuang's `5/8`.
* `rzThreeFifthsCircuit_failure_eq_pauliZ` — **on any other outcome, the circuit applies `Z`.** Each
  non-`(0,0)` branch operator equals `c · Z` for a scalar with `‖c‖² = 1/8` (so the three failure
  branches carry the complementary `3/8`).
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **`H` on each ancilla:** the gate `H ⊗ H ⊗ 1` on `qubit ⊗ (qubit ⊗ qubit)` — a Hadamard on
each of the two control (ancilla) qubits, identity on the target. -/
def rzThreeFifthsHadamards : Evolution (qubit.compose (qubit.compose qubit)) :=
  hadamardGate.tmul (hadamardGate.onLeft qubit)

/-- **The middle gate `T · (1⊗1⊗S) · T`:** two Toffoli gates (controls = the ancillas, target =
qubit 3) sandwiching the phase gate `S` on the target. -/
def rzThreeFifthsMiddle : Evolution (qubit.compose (qubit.compose qubit)) :=
  toffoliGate.comp (((sGate.onRight qubit).onRight qubit).comp toffoliGate)

/-- **The Figure 4.17 circuit** `(H⊗H) · T · (1⊗1⊗S) · T · (H⊗H)` on `qubit ⊗ (qubit ⊗ qubit)`:
two ancilla (control) qubits and one target, Hadamards on the ancillas at both ends. -/
def rzThreeFifthsCircuit : Evolution (qubit.compose (qubit.compose qubit)) :=
  rzThreeFifthsHadamards.comp (rzThreeFifthsMiddle.comp rzThreeFifthsHadamards)

/-- **The interference amplitude on the ancilla outcome `|a'⟩ ⊗ |b'⟩`** in the four-branch action
of the Figure 4.17 circuit on `|0⟩ ⊗ |0⟩ ⊗ |t⟩`: the sum over the two ancilla "histories" `(a, b)`
of the middle-gate phase `iᵗ⁺ᵃᵇ` (a Fin-2/XOR exponent) weighted by the Hadamard interference signs
`(-1)^{a·a'} (-1)^{b·b'}`, normalised by `(1/√2)⁴ = 1/4`. Reading off `rzThreeFifthsAmp 0 0 t` gives
the success operator `M₀₀`, and the other three `(a', b')` give the failure branches. -/
def rzThreeFifthsAmp (a' b' t : Fin 2) : ℂ :=
  Concrete.invSqrt2 ^ 4 * ∑ a : Fin 2, ∑ b : Fin 2,
    Complex.I ^ ((t + a * b : Fin 2) : ℕ) *
      ((-1 : ℂ) ^ ((a : ℕ) * (a' : ℕ)) * (-1 : ℂ) ^ ((b : ℕ) * (b' : ℕ)))

/-- **The rotation angle `θ` of Exercise 4.41:** `θ = arccos (3/5)`, so `cos θ = 3/5` (Nielsen &
Chuang's value) and `sin θ = 4/5`, hence `e^{iθ} = (3 + 4i)/5`. -/
def rzThreeFifthsAngle : ℝ := Real.arccos (3 / 5)

/-- `cos θ = 3/5` for the Exercise-4.41 angle — the value Nielsen & Chuang state for the applied
`R_z(θ)`. -/
theorem rzThreeFifthsAngle_cos : Real.cos rzThreeFifthsAngle = 3 / 5 := sorry

/-- **Exercise 4.41, success branch.

Because `R_z(θ)` is unitary, `‖c‖² = 5/8` is precisely the (input-independent) Born probability
of the `00` outcome — Nielsen & Chuang's `5/8` — and, after renormalising the post-measurement
state, the operation applied to the target is exactly the unitary `R_z(θ)`. The scalar `c` is
existential because its phase is a physically-irrelevant global phase; only `‖c‖²` carries
content. The identity is stated on each computational basis vector `|t⟩`, which (the two
spanning `M₀₀` and `c · R_z(θ)`) determines the operators.
-/
theorem rzThreeFifthsCircuit_success_eq_rotZ :
    ∃ c : ℂ, ‖c‖ ^ 2 = 5 / 8 ∧ ∀ t : Fin 2,
      rzThreeFifthsAmp 0 0 t • (qubitBasis t).vec
        = c • (rotZGate rzThreeFifthsAngle).op (qubitBasis t).vec := sorry

/-- **Exercise 4.41, failure branches: any other outcome applies `Z`.** For every ancilla outcome
`(a',b') ≠ (0,0)`, the (unnormalised) action on the target
`M_{a'b'} : |t⟩ ↦ rzThreeFifthsAmp a' b' t · |t⟩` equals `c · Z` for a scalar `c` with
`‖c‖² = 1/8`. So each of the three failure branches applies the Pauli `Z` (after renormalising),
each with Born probability `1/8` (totalling the complementary `3/8`). -/
theorem rzThreeFifthsCircuit_failure_eq_pauliZ (a' b' : Fin 2) (h : ¬ (a' = 0 ∧ b' = 0)) :
    ∃ c : ℂ, ‖c‖ ^ 2 = 1 / 8 ∧ ∀ t : Fin 2,
      rzThreeFifthsAmp a' b' t • (qubitBasis t).vec
        = c • pauliZGate.op (qubitBasis t).vec := sorry

end AxQM
