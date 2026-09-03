/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.ControlMeasurementCommute

/-!
# Nielsen & Chuang, Problem 5.3 (Kitaev's algorithm)

*(N&C p. 243.)*

Kitaev's algorithm: top qubit measured 0 with prob cos^2(pi phi); iterate U^k to extract bits of
phi.

* `measureObservableCircuit_bornProb_measure_control_zero` — on an eigenstate input
  `U|u⟩ = e^{2πiφ}|u⟩`, the control qubit is measured `0` with probability exactly `cos²(πφ)`.
* `measureObservableCircuit_bornProb_measure_control_zero_pow` — the iteration (`U → Uᵏ`): the same
  circuit with `Uᵏ` in place of `U` measures the control `0` with probability `cos²(πkφ)`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Problem 5.3 (Kitaev's algorithm).** With `|u⟩` an eigenstate
of `U` of eigenvalue `e^{2πiφ}`, running the Hadamard-controlled-`U` circuit on `|0⟩ ⊗ |u⟩` and
measuring the control (top) qubit in the computational basis yields outcome `0` with probability
exactly `cos²(πφ)`: ``` p(0) = cos²(πφ). ``` The target register `S` — where `|u⟩` lives — is
arbitrary. -/
theorem measureObservableCircuit_bornProb_measure_control_zero (U : Evolution S) (u : PureState S)
    (φ : ℝ) (h : U.HasEigenstate (Complex.exp (((2 * Real.pi * φ : ℝ) : ℂ) * Complex.I)) u) :
    (controlMeasurement S).bornProb
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0).tmul u)).toState 0
      = Real.cos (Real.pi * φ) ^ 2 := sorry

/-- **Nielsen & Chuang, Problem 5.3, the iteration `U → Uᵏ`.** With `|u⟩` an eigenstate of `U` of
eigenvalue `e^{2πiφ}`, running the circuit with `Uᵏ` in place of `U` measures the control `0`
with probability `cos²(πkφ)`. -/
theorem measureObservableCircuit_bornProb_measure_control_zero_pow (U : Evolution S)
    (u : PureState S) (φ : ℝ) (k : ℕ)
    (h : U.HasEigenstate (Complex.exp (((2 * Real.pi * φ : ℝ) : ℂ) * Complex.I)) u) :
    (controlMeasurement S).bornProb
        ((measureObservableCircuit (U ^ k)).evolvePure ((qubitBasis 0).tmul u)).toState 0
      = Real.cos (Real.pi * ((k : ℝ) * φ)) ^ 2 := sorry

end AxQM
