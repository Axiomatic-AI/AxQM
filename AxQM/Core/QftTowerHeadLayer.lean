/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QtowerSingleWireGate
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.HadamardGate
import AxQM.Core.QftRegisterBridge
import AxQM.Core.MultiControlledNotBasis

/-!
# The quantum Fourier transform's Figure 5.1 head layer (N&C Problem 5.2)

The **head layer** of the Figure 5.1 quantum Fourier transform circuit: a Hadamard on the head wire
`0` followed by the head control wire's cascade of controlled-`Rₖ` phase rotations onto every tail
wire.

## Main declarations
* `qftHeadRotationList n` — the head control wire's Figure 5.1 rotation phases: for each tail wire
  `t : Fin (n+1)`, the angle `2π·2^{t.rev}/2ⁿ⁺²` (`= 2π/2^{t+2}`, the QFT's `Rₜ₊₂`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The QFT head control wire's Figure 5.1 rotation phases.** For each tail wire `t : Fin (n+1)`,
the head control wire drives a controlled phase rotation of angle `2π·2^{t.rev}/2ⁿ⁺²` (equal to
`2π/2^{t+2}`, the quantum Fourier transform's `Rₜ₊₂`). -/
def qftHeadRotationList (n : ℕ) : List (Fin (n + 1) × ℝ) :=
  (List.finRange (n + 1)).map fun t => (t, 2 * Real.pi * 2 ^ (t.rev : ℕ) / 2 ^ (n + 2))

end AxQM
