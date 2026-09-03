/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.ProjectiveMeasurement
import AxQM.Basic.API.UnreadMeasurement

/-!
# AxQM — projective-measurement-then-conditional-unitary recovery (N&C Problem 10.1(2))

Nielsen & Chuang, Problem 10.1(2) assumes an error-correction procedure performed as *a projective
measurement followed by a conditional unitary operation* and asks how to turn one for a channel
`E₁` into one for an equivalent channel `E₂ = U ∘ E₁ ∘ V`. This file supplies the
vocabulary for that recovery form and the algebraic identity behind the transfer.

## Contents

* `AxQM.Measurement.conj` — conjugate a measurement by a unitary, `Mᵢ ↦ U Mᵢ U†`; and
  `AxQM.Measurement.IsProjective.conj` — this preserves projectivity (a unitary conjugate
  of an orthogonal projector is an orthogonal projector), so the transformed syndrome is again a
  projective measurement.
* `AxQM.Measurement.conjUnitary` — pre-compose each operator by a unitary, `Mᵢ ↦ Wᵢ Mᵢ`;
  the operators of the recovery `R` (its `unreadState` is `R`).
* `AxQM.ProjectiveUnitaryRecovery` — the bundled recovery: a projective syndrome
  measurement plus conditional unitaries; `apply` its channel action; and `conjugate U V` the
  transformed recovery with syndrome `{U Mᵢ U†}` and corrections `{V† Wᵢ U†}`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **Unitary cancellation on the state operators** `U† (U X) = X`. -/
theorem Evolution.star_op_mul_cancel (U : Evolution S) (X : S.space →L[ℂ] S.space) :
    star U.op * (U.op * X) = X := by
  have h : star U.op * U.op = 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
    exact U.adjoint_comp_self
  rw [← mul_assoc, h, one_mul]

namespace Measurement

/-- **Conjugating a measurement by a unitary evolution** `U`: the measurement with operators `Mᵢ ↦ U
Mᵢ U†`. Still a measurement — the completeness relation is conjugated, `∑ᵢ (U Mᵢ U†)† (U Mᵢ U†)
= U (∑ᵢ Mᵢ† Mᵢ) U† = U · 1 · U† = 1` (unitarity `U† U = U U† = 1`). -/
def conj (m : Measurement ι S) (U : Evolution S) : Measurement ι S where
  op i := U.op.comp ((m.op i).comp (adjoint U.op))
  complete := by
    have hUU' : U.op * adjoint U.op = 1 := by
      rw [ContinuousLinearMap.mul_def]; exact U.comp_adjoint_self
    have key : ∀ i, (adjoint (U.op.comp ((m.op i).comp (adjoint U.op)))).comp
          (U.op.comp ((m.op i).comp (adjoint U.op)))
        = U.op.comp (((adjoint (m.op i)).comp (m.op i)).comp (adjoint U.op)) := by
      intro i
      simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, star_mul,
        star_star, mul_assoc]
      simp only [Evolution.star_op_mul_cancel]
    rw [Finset.sum_congr rfl fun i _ => key i, ← comp_finset_sum, ← finset_sum_comp, m.complete]
    simp only [← ContinuousLinearMap.mul_def, one_mul]
    exact hUU'

/-- The operators of a unitary-conjugated measurement: `(m.conj U).op i = U Mᵢ U†`. -/
@[simp] theorem conj_op (m : Measurement ι S) (U : Evolution S) (i : ι) :
    (m.conj U).op i = U.op.comp ((m.op i).comp (adjoint U.op)) := rfl

/-- **A unitary conjugate of a projective measurement is projective.** Conjugating an orthogonal
projector `Mᵢ` by a unitary `U` gives the orthogonal projector `U Mᵢ U†` (self-adjoint:
`(U Mᵢ U†)† = U Mᵢ† U† = U Mᵢ U†`; idempotent: `(U Mᵢ U†)² = U Mᵢ (U† U) Mᵢ U† = U Mᵢ U†`), so the
conjugated syndrome measurement is again a projective measurement — the transferred procedure is "in
the same fashion". -/
theorem IsProjective.conj {m : Measurement ι S} (h : m.IsProjective) (U : Evolution S) :
    (m.conj U).IsProjective := by
  intro i
  rw [conj_op]
  refine ⟨?_, ?_⟩
  · -- idempotent: `(U Mᵢ U†)(U Mᵢ U†) = U Mᵢ U†`
    have hidem : m.op i * m.op i = m.op i := (h i).isIdempotentElem
    change (U.op.comp ((m.op i).comp (adjoint U.op))) * (U.op.comp ((m.op i).comp (adjoint U.op)))
        = U.op.comp ((m.op i).comp (adjoint U.op))
    simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, mul_assoc]
    simp only [Evolution.star_op_mul_cancel]
    rw [← mul_assoc (m.op i) (m.op i), hidem]
  · -- self-adjoint: `(U Mᵢ U†)† = U Mᵢ U†`
    have hsa : star (m.op i) = m.op i := (h i).isSelfAdjoint.star_eq
    change star (U.op.comp ((m.op i).comp (adjoint U.op)))
        = U.op.comp ((m.op i).comp (adjoint U.op))
    simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, star_mul,
      star_star, hsa, mul_assoc]

/-- **Pre-composing each measurement operator by a unitary** `Wᵢ`: the measurement with operators
`Mᵢ ↦ Wᵢ Mᵢ`. Still a measurement — `∑ᵢ (Wᵢ Mᵢ)† (Wᵢ Mᵢ) = ∑ᵢ Mᵢ† Wᵢ† Wᵢ Mᵢ = ∑ᵢ Mᵢ† Mᵢ = 1`
(unitarity `Wᵢ† Wᵢ = 1`). -/
def conjUnitary (m : Measurement ι S) (W : ι → Evolution S) : Measurement ι S where
  op i := (W i).op.comp (m.op i)
  complete := by
    have key : ∀ i, (adjoint ((W i).op.comp (m.op i))).comp ((W i).op.comp (m.op i))
        = (adjoint (m.op i)).comp (m.op i) := by
      intro i
      simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, star_mul,
        mul_assoc]
      simp only [Evolution.star_op_mul_cancel]
    rw [Finset.sum_congr rfl fun i _ => key i]
    exact m.complete

end Measurement

/-- **A projective-measurement-then-conditional-unitary recovery** (Nielsen & Chuang, Problem
10.1(2)): a projective syndrome **measurement** `meas` (`Measurement.IsProjective`) together
with a family of conditional **unitary** corrections `corr`. This is the concrete form N&C
assumes the error-correction procedure takes. -/
structure ProjectiveUnitaryRecovery (ι : Type*) [Fintype ι] (S : QSystem) where
  /-- The syndrome measurement. -/
  meas : Measurement ι S
  /-- The syndrome measurement is projective (its operators are orthogonal projectors). -/
  proj : meas.IsProjective
  /-- The conditional unitary corrections `Wᵢ`, one per measurement outcome. -/
  corr : ι → Evolution S

namespace ProjectiveUnitaryRecovery

variable (R : ProjectiveUnitaryRecovery ι S)

/-- **The action of a projective-unitary recovery** `R(ρ) = ∑ᵢ Wᵢ Mᵢ ρ Mᵢ† Wᵢ†`: measure the
syndrome `{Mᵢ}`, then apply the conditional unitary `Wᵢ`. It is the unread (non-selective)
post-measurement state (`Measurement.unreadState`) of the measurement with operators `Wᵢ Mᵢ`
(`Measurement.conjUnitary`), hence a genuine `State` and a CPTP channel. -/
def apply (ρ : State S) : State S := (R.meas.conjUnitary R.corr).unreadState ρ

/-- **The recovery transformed for an equivalent channel** `E₂ = U ∘ E₁ ∘ V`: syndrome measurement
`{U Mᵢ U†}` (`Measurement.conj`) and conditional unitaries `{V† Wᵢ U†}`. Projectivity of the new
syndrome is `Measurement.IsProjective.conj`. -/
def conjugate (U V : Evolution S) : ProjectiveUnitaryRecovery ι S where
  meas := R.meas.conj U
  proj := R.proj.conj U
  corr i := V.adjoint.comp ((R.corr i).comp U.adjoint)

end ProjectiveUnitaryRecovery

end AxQM
