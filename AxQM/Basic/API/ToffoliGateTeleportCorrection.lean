/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ToffoliGateTeleportMeasure
import AxQM.Basic.API.RelativePhaseToffoli
import AxQM.Basic.API.ToffoliPauliPropagation

/-!
# AxQM.Basic.API — the byproduct correction of Toffoli gate teleportation

The **classically-controlled correction stage** of the fault-tolerant Toffoli gate-teleportation
circuit of Nielsen & Chuang **Exercise 10.68** (the Figure on p. 488, part (2)) — the final piece of
the measured gate-teleportation identity.

## Main declarations
* `evolPow m U` — the gate `U` applied *conditioned on the classical outcome bit* `m` (`U^m`:
  identity if `m = 0`, `U` if `m = 1`), with which the outcome-dependent byproduct corrections are
  assembled.

* `toffoliTeleportControlCorrection m₁ m₂` — the classically-controlled **`X`-byproduct correction**
  `CNOT₁₃^{m₂} X₂^{m₂} CNOT₂₃^{m₁} X₁^{m₁}`.

* `toffoliTeleportCorrection m₁ m₂ m₃` — the **full** classically-controlled correction `Bₘ†`
  (control corrections followed by the target phase correction `Z₃^{m₃} CZ₁₂^{m₃}`).
-/

open scoped TensorProduct InnerProductSpace

noncomputable section

namespace AxQM

/-- **A gate applied conditioned on a classical outcome bit** `m : Fin 2`: `U^m`, i.e. the identity
when `m = 0` and `U` when `m = 1`. The `Evolution`-level analogue of the single-qubit
`targetXPow`. -/
def evolPow {S : QSystem} (m : Fin 2) (U : Evolution S) : Evolution S :=
  if m = 0 then Evolution.id else U

/-- **The classically-controlled `X`-byproduct correction** of Exercise 10.68, conditioned on the
two control-qubit (`Z`-basis) measurement outcomes `(m₁, m₂)`:

`CNOT₁₃^{m₂} · X₂^{m₂} · CNOT₂₃^{m₁} · X₁^{m₁}`

— the inverse `Bₘ†` of the propagated `X` byproducts `X₁^{m₁} CNOT₂₃^{m₁} · X₂^{m₂} CNOT₁₃^{m₂}`
that the Exercise 10.67 rules deposit when the Toffoli is moved left past `X₁^{m₁} X₂^{m₂}`.
-/
def toffoliTeleportControlCorrection (m₁ m₂ : Fin 2) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (evolPow m₂ cnotFirstThirdGate).comp
    ((evolPow m₂ ((pauliXGate.onLeft qubit).onRight qubit)).comp
      ((evolPow m₁ (cnotGate.onRight qubit)).comp
        (evolPow m₁ (pauliXGate.onLeft (qubit ⊗ qubit)))))

/-- **The full classically-controlled correction** `Bₘ†` of Exercise 10.68. This is the complete
correction the fault-tolerant circuit applies, exercising all three Exercise 10.67 propagation
rules. -/
def toffoliTeleportCorrection (m₁ m₂ m₃ : Fin 2) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (evolPow m₃ controlledZLeftGate).comp
    ((evolPow m₃ ((pauliZGate.onRight qubit).onRight qubit)).comp
      (toffoliTeleportControlCorrection m₁ m₂))

end AxQM
