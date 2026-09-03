/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QftRegisterBridge
import AxQM.Core.MultiControlledNotBasis
import AxQM.Core.QtowerHadamardLayer
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.ControlMeasurementCommute
import AxQM.Core.MultiControlledReduction
import AxQM.Basic.API.Associator
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.InverseQuantumFourierTransform
import AxQM.Basic.API.ControlledControlledUnitary

/-!
# The inverse-QFT readout on the control register (N&C §5.2, Figure 5.2, last stage)

The final stage of the phase-estimation circuit (N&C Figure 5.2) applies the **inverse quantum
Fourier transform to the `t`-qubit control register**, leaving the target register alone. Run on the
phase-gradient superposition `⊗_w |+_{2^w·θ}⟩ ⊗ |u⟩` produced by the controlled powers, it reads
the eigenphase `θ/2π` back into the control register.

## Main declarations
* `qtowerSplitControl n S` — the **control–target split** `qtower (n+1) S ≃ₛ (qtower n qubit) ⊗ S`:
  it pulls the target `S` out from the bottom of the `(n+1)`-control register to a trailing factor,
  gathering the `n+1` control qubits into the pure tower `qtower n qubit`.
* `qftTowerInverseEvolution n` — the **inverse tower QFT** `Evolution.congr (quditPowTower n)
  (qftInverseEvolution (2^{n+1}))` on `qtower n qubit`, the register-tower transport of the inverse
  QFT (Ex 5.5).
* `qtowerControlInverseQft n S` — the **inverse-QFT readout gate** on the phase-estimation register
  `qtower (n+1) S`: the inverse tower QFT applied to the control qubits (through the split), the
  identity on the target `S`. This is Figure 5.2's terminal box.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The control–target split** `qtower (n+1) S ≃ₛ (qtower n qubit) ⊗ S`: separate the `n+1`
control qubits (gathered into the pure tower `qtower n qubit`) from the target `S`, pulled out
to a trailing factor. -/
def qtowerSplitControl : (n : ℕ) → (S : QSystem) → (qtower (n + 1) S).Iso ((qtower n qubit) ⊗ S)
  | 0, S => QSystem.Iso.refl (qubit ⊗ S)
  | (n + 1), S =>
      ((QSystem.Iso.refl qubit).tmul (qtowerSplitControl n S)).trans
        (QSystem.assoc qubit (qtower n qubit) S)

/-- **The inverse tower QFT** on the pure control register `qtower n qubit`: the inverse quantum
Fourier transform `qftInverseEvolution (2^{n+1})` (Ex 5.5) of the single `2^{n+1}`-level register,
transported onto the `(n+1)`-qubit tower along the register bridge `quditPowTower n`. The
`Evolution` undoing `qftTowerEvolution n`. -/
def qftTowerInverseEvolution (n : ℕ) : Evolution (qtower n qubit) :=
  Evolution.congr (quditPowTower n) (qftInverseEvolution (2 ^ (n + 1)))

/-- **The inverse-QFT readout gate** on the phase-estimation register `qtower (n+1) S`: the inverse
tower QFT `qftTowerInverseEvolution n` applied to the `n+1` control qubits — through the
control–target split `qtowerSplitControl n S` — and the identity on the target `S`. This is the
terminal box of N&C Figure 5.2, the inverse quantum Fourier transform on the control register that
reads the eigenphase back into the estimate register. -/
def qtowerControlInverseQft (n : ℕ) (S : QSystem) : Evolution (qtower (n + 1) S) :=
  Evolution.congr (qtowerSplitControl n S).symm ((qftTowerInverseEvolution n).onLeft S)

end AxQM
