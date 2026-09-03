/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledPhaseShift
import AxQM.Basic.API.ControlledZ
import AxQM.NC.Ch4.Exercise4_17

/-!
# Nielsen & Chuang, Exercise 7.23 (a universal two-qubit gate from the optical Kerr gate)

*(N&C p. 308.)*

Show the two-qubit gate (7.87) plus single-qubit ops realizes a controlled-NOT for any φ_a,φ_b, Δ=π.

* `opticalKerrGate` — the two-qubit optical logic gate (7.87), as an `Evolution` on `qubit ⊗ qubit`.
* `cnotGate_eq_singleQubit_conj_opticalKerrGate` — Exercise 7.23: for any `ϕ_a, ϕ_b` and `Δ = π`,
  single-qubit gates conjugate that gate into a `CNOT`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **The two-qubit optical logic gate (7.87)** of Nielsen & Chuang §7.5.4, as an `Evolution` on
`qubit ⊗ qubit`. Following N&C's physical model (p. 307) — a probe photon acquires the phase
`e^{iϕ_a}`, a pump photon acquires `e^{iϕ_b}`, and the two-photon state acquires an additional Kerr
phase `Δ` — in the computational basis it is the diagonal gate
`diag(1, e^{iϕ_a}, e^{iϕ_b}, e^{i(ϕ_a + ϕ_b + Δ)})`, i.e. the matrix (7.87). -/
def opticalKerrGate (φa φb Δ : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((phaseShiftGate φb).onLeft qubit).comp
    (((phaseShiftGate φa).onRight qubit).comp (controlledPhaseShift Δ))

/-- **Nielsen & Chuang, Exercise 7.23: the optical gate (7.87) plus single-qubit operations realises
a `CNOT`.** For any single-photon phases `ϕ_a, ϕ_b` and the Kerr value `Δ = π`,

`CNOT = (1 ⊗ H) · [(P(-ϕ_b) ⊗ 1) · (1 ⊗ P(-ϕ_a)) · opticalKerrGate ϕ_a ϕ_b π] · (1 ⊗ H)`,

a full equality of gate `Evolution`s. Thus the two-qubit gate (7.87), augmented with arbitrary
single-qubit operations, realises a controlled-`NOT`.
-/
theorem cnotGate_eq_singleQubit_conj_opticalKerrGate (φa φb : ℝ) :
    cnotGate = (hadamardGate.onRight qubit).comp
      ((((phaseShiftGate (-φb)).onLeft qubit).comp
            (((phaseShiftGate (-φa)).onRight qubit).comp (opticalKerrGate φa φb Real.pi))).comp
        (hadamardGate.onRight qubit)) := sorry

end AxQM
