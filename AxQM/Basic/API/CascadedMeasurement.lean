/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Measurement

/-!
# AxQM — the cascade of two measurements

The **cascade** generator `L.cascade M`: given a measurement `L` (outcomes `κ`) and a
measurement `M` (outcomes `μ`), the composite that measures `L` and then `M` is itself a single
measurement, with outcome set `κ × μ`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {κ μ : Type*} [Fintype κ] [Fintype μ] {S : QSystem}

namespace Measurement

/-- The **cascade** of two measurements `L` (outcomes `κ`) and `M` (outcomes `μ`): the single
measurement with outcome set `κ × μ` whose operator for outcome `(l, m)` is `N₍ₗ,ₘ₎ = Mₘ Lₗ`,
with completeness `∑₍ₗ,ₘ₎ N₍ₗ,ₘ₎† N₍ₗ,ₘ₎ = 1`. -/
def cascade (L : Measurement κ S) (M : Measurement μ S) : Measurement (κ × μ) S where
  op p := (M.op p.2).comp (L.op p.1)
  complete := by
    rw [← L.complete, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hsummand : ∀ m : μ,
        (adjoint ((M.op m).comp (L.op l))).comp ((M.op m).comp (L.op l))
          = (adjoint (L.op l)).comp (((adjoint (M.op m)).comp (M.op m)).comp (L.op l)) :=
      fun m => by rw [adjoint_comp, comp_assoc, comp_assoc]
    simp only [hsummand]
    rw [← ContinuousLinearMap.comp_finset_sum, ← ContinuousLinearMap.finset_sum_comp, M.complete,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

@[simp]
theorem cascade_op (L : Measurement κ S) (M : Measurement μ S) (l : κ) (m : μ) :
    (L.cascade M).op (l, m) = (M.op m).comp (L.op l) := rfl

/-- The post-measurement operation of the cascade factors through the two individual
post-measurement operations: `E₍ₗ,ₘ₎(ρ) = Mₘ Lₗ ρ Lₗ† Mₘ† = Eₘ(Eₗ(ρ))`. -/
theorem postOp_cascade (L : Measurement κ S) (M : Measurement μ S) (ρ : S →L[ℂ] S) (l : κ) (m : μ) :
    ContinuousLinearMap.postOp (L.cascade M).op ρ (l, m)
      = ContinuousLinearMap.postOp M.op (ContinuousLinearMap.postOp L.op ρ l) m := by
  simp only [ContinuousLinearMap.postOp, cascade_op, adjoint_comp, comp_assoc]

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- **Born probabilities depend only on the outcome operator.** If two measurements have the same
operator at a pair of outcomes (`m₁.op i = m₂.op j`), those outcomes have equal Born probability in
every state. -/
theorem bornProb_congr {m₁ : Measurement ι₁ S} {m₂ : Measurement ι₂ S} {i : ι₁} {j : ι₂}
    (h : m₁.op i = m₂.op j) (ρ : State S) : m₁.bornProb ρ i = m₂.bornProb ρ j := by
  rw [Measurement.bornProb_eq_re_trace_postOp, Measurement.bornProb_eq_re_trace_postOp,
    ContinuousLinearMap.postOp, ContinuousLinearMap.postOp, h]

end Measurement

end AxQM
