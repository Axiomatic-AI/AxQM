/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Measurement
import AxQM.Basic.Evolution
import AxQM.Basic.API.DeferredMeasurementReindex
import AxQM.Basic.API.DeferredMeasurement
import AxQM.Basic.API.ControlMeasurementCommute

/-!
# Nielsen & Chuang, Exercise 4.35 (measurement commutes with controls)

*(N&C p. 188.)*

Prove measurement commutes with a gate when the measured qubit is the control.

* `controlMeasurement_commute_bornProb` — the outcome statistics agree: the Born probability of
  outcome `i` is the same whether the control is measured before or after `C(U)`, `p(i ∣ C(U) ρ
  C(U)†) = p(i ∣ ρ)`.
* `controlMeasurement_commute_postMeasurement` — the post-measurement states agree: measuring the
  control after `C(U)` yields exactly the classically-controlled gate `Wᵢ` applied to the state
  obtained by measuring the control first, `postMeas(C(U) ρ C(U)†, i) = Wᵢ · postMeas(ρ, i)`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Exercise 4.35 (measurement statistics).** Measuring the control qubit commutes with the
controlled gate `C(U)` at the level of the Born probabilities. The instance at `m =
controlMeasurement S`, `V = controlledUnitary U`, `W = classicalControl U` of the
deferred-measurement Born-rule invariance `Measurement.bornProb_evolve_of_comm`, whose
commutation hypothesis is `controlMeasurement_op_comp_controlledUnitary`. -/
theorem controlMeasurement_commute_bornProb (U : Evolution S) (ρ : State (qubit ⊗ S)) (i : Fin 2) :
    (controlMeasurement S).bornProb ((controlledUnitary U).evolve ρ) i
      = (controlMeasurement S).bornProb ρ i :=
  Measurement.bornProb_evolve_of_comm (controlMeasurement S) (controlledUnitary U)
    (classicalControl U) (controlMeasurement_op_comp_controlledUnitary U) ρ i

/-- **Exercise 4.35 (post-measurement state, the first equality).** Measuring the control qubit
commutes with the controlled gate `C(U)` at the level of the collapsed state.

`postMeas(C(U) ρ C(U)†, i) = Wᵢ · postMeas(ρ, i)`.

This is N&C's first equality: the left circuit (gate then measure) equals the right circuit
(measure then classically-controlled gate).
-/
theorem controlMeasurement_commute_postMeasurement (U : Evolution S) (ρ : State (qubit ⊗ S))
    (i : Fin 2) (hp : (controlMeasurement S).bornProb ρ i ≠ 0) :
    (controlMeasurement S).postMeasurement ((controlledUnitary U).evolve ρ) i
        (by rw [controlMeasurement_commute_bornProb]; exact hp)
      = (classicalControl U i).evolve ((controlMeasurement S).postMeasurement ρ i hp) := sorry

end AxQM
