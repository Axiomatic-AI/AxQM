/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledUnitaryDecomposition

/-!
# AxQM.Basic.API — the controlled phase-shift gate `C(P(φ))`

The operator-level form of the quantum-Fourier-transform circuit's two-qubit gate (Nielsen &
Chuang, §5.1): the controlled phase-shift gate `C(P(φ))` on two qubits, the controlled version of
the single-qubit phase gate `P(φ) = phaseShiftGate φ = diag(1, exp(iφ))`.
-/

noncomputable section

namespace AxQM

/-- The **controlled phase-shift gate** `C(P(φ)) = |0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ P(φ)` on `qubit ⊗ qubit`
(control qubit on the left), Nielsen & Chuang's controlled phase rotation — the *only* kind of
two-qubit gate appearing in the quantum-Fourier-transform circuit (§5.1). Defined as the
`controlledUnitary` instance at the phase-shift gate `P(φ) = phaseShiftGate φ = diag(1, exp(iφ))`.
The QFT's phase gate `C(R_k)` is the instance `φ = 2π/2ᵏ`. -/
def controlledPhaseShift (φ : ℝ) : Evolution (qubit ⊗ qubit) :=
  controlledUnitary (phaseShiftGate φ)

end AxQM
