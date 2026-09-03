/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.MeasurementOperation
import AxQM.Basic.API.ProjectiveMeasurement
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# AxQM — the unread (non-selective) post-measurement state (N&C Exercise 4.32, part 1)

When a measurement `m` is performed but its outcome is **not learned**,
the state assigned to the system is the *non-selective* (unread) post-measurement state: the
ensemble of the collapsed branches weighted by their Born probabilities. At the operator level this
is the operator-sum (Kraus) map of the measurement operators applied to `ρ`,

## Contents

* `Measurement.unreadState` — the unread/non-selective post-measurement state `ρ' = Σᵢ Mᵢ ρ Mᵢ†`,
  as a genuine `State` (density operator), built on the Kraus map `ContinuousLinearMap.krausSumₗ`.
* `Measurement.IsProjective.unreadState_op` — the literal N&C form for a **projective** measurement
  (`Mᵢ = Pᵢ` orthogonal projectors, so `Mᵢ† = Mᵢ`): `ρ' = Σᵢ Pᵢ ρ Pᵢ` (Eq. (4.40) with
  `P₀ = |0⟩⟨0|`, `P₁ = |1⟩⟨1|` the special two-outcome case in the exercise text).
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- The **unread (non-selective) post-measurement state** `ρ' = Σᵢ Mᵢ ρ Mᵢ†` (Nielsen–Chuang
Exercise 4.32, Eq. (4.40)): the state assigned after the measurement `m` when the outcome is *not*
learned — the Born-weighted mixture of the collapsed branches. It is a genuine density operator:
positivity is `krausSumₗ_isPositive` (each `Mᵢ ρ Mᵢ†` is positive), and trace one is
`trace_krausSumₗ` together with completeness `Σᵢ Mᵢ† Mᵢ = 1` (`m.complete`), which turns
`tr(Σᵢ Mᵢ ρ Mᵢ†) = tr((Σᵢ Mᵢ† Mᵢ) ρ)` into `tr(ρ) = 1`. -/
def unreadState (m : Measurement ι S) (ρ : State S) : State S where
  op := krausSumₗ m.op ρ.op
  isDensity := by
    refine ⟨krausSumₗ_isPositive m.op ρ.isPositive_op, ?_⟩
    rw [trace_krausSumₗ, m.complete, one_def, id_comp]
    exact ρ.trace_op_eq_one

/-- **Nielsen–Chuang Exercise 4.32, Eq. (4.40), projective form.** For a *projective* measurement —
one whose operators are orthogonal projectors `Mᵢ = Pᵢ` (`Measurement.IsProjective`), so `Mᵢ† = Mᵢ`
— the unread post-measurement state is `ρ' = Σᵢ Pᵢ ρ Pᵢ`, the literal statement of Eq. (4.40) (the
`P₀ = |0⟩⟨0|`, `P₁ = |1⟩⟨1|` two-outcome projective measurement of the exercise text is this special
case). -/
theorem IsProjective.unreadState_op {m : Measurement ι S} (h : m.IsProjective) (ρ : State S) :
    (m.unreadState ρ).op = ∑ i, (m.op i).comp (ρ.op.comp (m.op i)) := sorry

end Measurement

end AxQM
