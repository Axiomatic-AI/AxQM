/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.RzThreeFifthsMeasurement

/-!
# Nielsen & Chuang, Exercise 4.41 (Fig 4.17 — a measurement-based `R_z(θ)`, `cos θ = 3/5`)

*(N&C p. 197.)*

Show the circuit of Fig 4.17 applies R_z(theta) with cos theta=3/5 on success.

* `rzThreeFifthsCircuit_bothZero_bornProb` — the probability of both ancilla outcomes being `0` is
  `5/8`, for every target `|ψ⟩`. Running the explicit two-ancilla `Measurement`
  `rzTwoAncillaMeasurement` after the circuit on `|0,0,ψ⟩` gives outcome `(0,0)` with Born
  probability exactly `5/8` for an arbitrary (normalised) single-qubit target `|ψ⟩` — N&C's second
  explicit claim, input-independent.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.41 — the success probability is `5/8`, for every target `|ψ⟩`.**
Measuring both ancilla qubits of the Figure 4.17 circuit in the computational basis
(`rzTwoAncillaMeasurement`) after the circuit acts on `|0,0,ψ⟩`, the outcome "both `0`" occurs
with Born probability exactly `5/8` — Nielsen & Chuang's value — for *any* (normalised)
single-qubit target `|ψ⟩`. Input-independence is exactly N&C's claim about the probability of both
measurement outcomes being `0`. -/
theorem rzThreeFifthsCircuit_bothZero_bornProb (ψ : PureState qubit) :
    rzTwoAncillaMeasurement.bornProb
        (rzThreeFifthsCircuit.evolvePure ((qubitBasis 0).tmul ((qubitBasis 0).tmul ψ))).toState
        (0, 0)
      = 5 / 8 := sorry

end AxQM
