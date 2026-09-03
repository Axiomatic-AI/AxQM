/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QftRegisterBridge
import AxQM.Core.MultiControlledNotBasis
import AxQM.Basic.API.ControlMeasurementCommute
import AxQM.Basic.API.CascadedMeasurement
import AxQM.Basic.API.MeasurementReindex
import AxQM.Basic.Measurement
import AxQM.Basic.API.QuditMeasurement
import AxQM.Basic.API.MeasurementOperation
import AxQM.Basic.API.PureState

/-!
# The terminal per-wire measurement on the control tower (N&C Problem 5.2)

The measured quantum Fourier transform ends by measuring **every wire** of the output register in
the computational basis, here as a wire-addressed measurement on the `(n+1)`-qubit control tower
`qtower n qubit`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The terminal per-wire computational-basis measurement on the control tower.**
`qtowerMeasurement n` measures all `n+1` wires of `qtower n qubit` in the computational basis,
recording the bit-string `Fin (n+1) → Fin 2` of outcomes. Built head-first to match the tower
recursion. -/
def qtowerMeasurement : (n : ℕ) → Measurement (Fin (n + 1) → Fin 2) (qtower n qubit)
  | 0 => (quditMeasurement 2).reindexOutcome (Equiv.funUnique (Fin 1) (Fin 2))
  | n + 1 =>
      ((controlMeasurement (qtower n qubit)).cascade
        ((qtowerMeasurement n).onRight qubit)).reindexOutcome
          (Fin.consEquiv (fun _ : Fin (n + 2) => Fin 2)).symm

/-- The wire↔register-index relabelling `b ↦ |finFunctionFinEquiv (b ∘ Fin.rev)⟩`: a tower wire
bit-string is read as the little-endian register index after the `Fin.rev` endianness flip. It
relabels the register's `Fin (2ⁿ⁺¹)` outcome set to the tower's `Fin (n+1) → Fin 2` wire
outcomes. -/
def towerMeasurementOutcomeEquiv (n : ℕ) : (Fin (n + 1) → Fin 2) ≃ Fin (2 ^ (n + 1)) :=
  (Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 2))).trans finFunctionFinEquiv

end AxQM
