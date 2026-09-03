/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledPhaseShift
import AxQM.Basic.API.ControlledRotation
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.PiEighthGate
import AxQM.Basic.API.HadamardRotation

/-!
# Nielsen & Chuang, Exercise 5.4 — decomposing the controlled-`R_k` gate

*(N&C p. 221.)*

Give a decomposition of the controlled-R_k gate into single-qubit and CNOT gates.

* `controlledRk_eq_cnot_circuit`
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 5.4: decomposition of the controlled-`R_k` gate.** The quantum
Fourier transform's phase gate `R_k = P(2π/2ᵏ) = diag(1, exp(2πi/2ᵏ))` (N&C eq. 5.11) has its
controlled version decomposed into single-qubit gates and two `CNOT`s,

`C(R_k) = (P(π/2ᵏ) ⊗ 1) · (1 ⊗ R_z(π/2ᵏ)) · CNOT · (1 ⊗ R_z(-π/2ᵏ)) · CNOT`,

the exact two-qubit gate of the QFT circuit expressed with only one-qubit gates and `CNOT`s. -/
theorem controlledRk_eq_cnot_circuit (k : ℕ) :
    controlledPhaseShift (2 * Real.pi / 2 ^ k) =
      ((phaseShiftGate (2 * Real.pi / 2 ^ k / 2)).onLeft qubit).comp
        ((((rotZGate (2 * Real.pi / 2 ^ k / 2)).onRight qubit).comp cnotGate).comp
          (((rotZGate (-(2 * Real.pi / 2 ^ k / 2))).onRight qubit).comp cnotGate)) := sorry

end AxQM
