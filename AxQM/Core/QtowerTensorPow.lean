/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledNotBasis
import AxQM.Basic.API.TensorPowSplit
import AxQM.Basic.API.Associator
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.PiTensorState

/-!
# The `qtower ↔ tensor-power` structural bridge (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit implementing
`Cⁿ(X)`.

## Main declarations
* `qtowerQubitTensorPow n` — the **bridge** `qtower n qubit ≃ₛ qubit ^⊗ₛ (n+1)`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **The `qtower ↔ tensor-power` bridge** `qtower n qubit ≃ₛ qubit ^⊗ₛ (n+1)`: the system
isomorphism identifying the right-nested `(n+1)`-qubit control tower `qtower n qubit` with the
symmetric `(n+1)`-fold power `qubit ^⊗ₛ (n+1)`. -/
def qtowerQubitTensorPow : (n : ℕ) → (qtower n qubit).Iso (qubit ^⊗ₛ (n + 1))
  | 0 => qubit.tensorPowOne
  | n + 1 =>
      ((QSystem.Iso.refl qubit).tmul (qtowerQubitTensorPow n)).trans
        (QSystem.tensorPowSuccHead qubit (n + 1)).symm

end AxQM
