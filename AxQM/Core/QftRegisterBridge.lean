/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuditDimCongr
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.QuantumFourierTransform
import AxQM.Basic.API.QuditGate
import AxQM.Concrete.QftGateCircuit
import AxQM.Concrete.QuantumFourierTransform
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.LeftPairGate
import AxQM.Core.MultiControlledReduction

/-!
# The measured-QFT register bridge `qudit (2ⁿ⁺¹) ≃ₛ qtower n qubit` (N&C Problem 5.2)

The quantum Fourier transform enters as an `Evolution` on the *single* register `qudit (2ⁿ)`
(as `qftEvolution (2ⁿ)`). The whole-circuit measured-QFT reduction instead needs the QFT on an
explicit **`n`-qubit tensor register**, so that a terminal per-wire computational-basis
measurement can be deferred wire by wire, on the *right-nested* control tower `qtower n qubit`.

## Main declarations
* `quditPowTower n` — the **register bridge** `qudit (2ⁿ⁺¹) ≃ₛ qtower n qubit`, identifying the
  `2ⁿ⁺¹`-level register with the right-nested `(n+1)`-qubit control tower.
* `qftTowerEvolution n` — the **QFT transported onto the tower**, `Evolution.congr (quditPowTower n)
  (qftEvolution (2ⁿ⁺¹))`: the quantum Fourier transform as an `Evolution` on `qtower n qubit`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The measured-QFT register bridge** `qudit (2ⁿ⁺¹) ≃ₛ qtower n qubit`: the system isomorphism
identifying the `2ⁿ⁺¹`-level register (on which the quantum Fourier transform `qftEvolution
(2ⁿ⁺¹)` lives) with the right-nested `(n+1)`-qubit control tower `qtower n qubit`. Built by
induction on `n`. -/
def quditPowTower : (n : ℕ) → (qudit (2 ^ (n + 1))) ≃ₛ (qtower n qubit)
  | 0 => QSystem.Iso.refl qubit
  | n + 1 =>
      (quditDimCongr (pow_succ' 2 (n + 1))).trans
        ((quditProdIso 2 (2 ^ (n + 1))).trans
          ((QSystem.Iso.refl qubit).tmul (quditPowTower n)))

/-- **The quantum Fourier transform transported onto the qubit tower.** The QFT `qftEvolution
(2ⁿ⁺¹)` of the single register `qudit (2ⁿ⁺¹)`, carried onto the right-nested `(n+1)`-qubit
control tower `qtower n qubit` along the register bridge `quditPowTower n`. -/
def qftTowerEvolution (n : ℕ) : Evolution (qtower n qubit) :=
  Evolution.congr (quditPowTower n) (qftEvolution (2 ^ (n + 1)))

end AxQM
