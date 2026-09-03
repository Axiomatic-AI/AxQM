/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Measurement
import AxQM.Basic.Evolution

/-!
# AxQM — deferring a basis-permuting gate past a measurement

A gate that *permutes* the measurement basis (a swap network, a wire relabelling) does not commute
with the measurement operators up to a fixed outcome — `Mᵢ V = Wᵢ Mᵢ`; it carries the operator of
one outcome onto that of *another*, `Mᵢ V = Wᵢ M_{e i}`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- **Branch-map identity for deferring a basis-permuting gate past a measurement.** If each
measurement operator `Mᵢ` of `m` carries the gate `V` onto the *reindexed* operator `M_{e i}` up to
an outcome-gate `Wᵢ` — `Mᵢ V = Wᵢ M_{e i}` (`hcomm`) — then the unnormalized post-measurement
operator of outcome `i` on the *evolved* state `V ρ V†` equals `Wᵢ` conjugating the branch of `ρ`
at the reindexed outcome `e i`:

  `Eᵢ(V ρ V†) = Mᵢ (V ρ V†) Mᵢ† = Wᵢ (M_{e i} ρ M_{e i}†) Wᵢ† = Wᵢ E_{e i}(ρ) Wᵢ†`. -/
theorem postOp_evolve_of_reindex_comm (m : Measurement ι S) (V : Evolution S) (W : ι → Evolution S)
    (e : ι ≃ ι) (hcomm : ∀ i, (m.op i).comp V.op = (W i).op.comp (m.op (e i))) (ρ : State S)
    (i : ι) :
    ContinuousLinearMap.postOp m.op (V.evolve ρ).op i
      = (W i).op.comp ((ContinuousLinearMap.postOp m.op ρ.op (e i)).comp (adjoint (W i).op)) := by
  have conj_comp : ∀ A B X : S.space →L[ℂ] S.space,
      (A.comp B).comp (X.comp (adjoint (A.comp B)))
        = A.comp ((B.comp (X.comp (adjoint B))).comp (adjoint A)) := by
    intro A B X
    rw [ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.comp_assoc]
  simp only [ContinuousLinearMap.postOp, Evolution.evolve_op]
  rw [← conj_comp (m.op i) V.op ρ.op, hcomm i, conj_comp (W i).op (m.op (e i)) ρ.op]

/-- **The two branch traces agree:** `tr Eᵢ(V ρ V†) = tr E_{e i}(ρ)`. -/
theorem trace_postOp_evolve_of_reindex_comm (m : Measurement ι S) (V : Evolution S)
    (W : ι → Evolution S) (e : ι ≃ ι)
    (hcomm : ∀ i, (m.op i).comp V.op = (W i).op.comp (m.op (e i))) (ρ : State S) (i : ι) :
    LinearMap.trace ℂ S.space (ContinuousLinearMap.postOp m.op (V.evolve ρ).op i : S.space →ₗ[ℂ] _)
      = LinearMap.trace ℂ S.space
          (ContinuousLinearMap.postOp m.op ρ.op (e i) : S.space →ₗ[ℂ] _) := by
  rw [postOp_evolve_of_reindex_comm m V W e hcomm ρ i, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_comp, LinearMap.trace_comp_cycle, ← ContinuousLinearMap.coe_comp,
    (W i).adjoint_comp_self, ContinuousLinearMap.coe_one, Module.End.one_eq_id, LinearMap.comp_id]

/-- **Outcome probabilities are relabelled when a basis-permuting gate is deferred**:
under `Mᵢ V = Wᵢ M_{e i}`, the Born probability of outcome `i` on `V ρ V†` equals that of the
relabelled outcome `e i` on `ρ`, `p(i ∣ V ρ V†) = p(e i ∣ ρ)`. -/
theorem bornProb_evolve_of_reindex_comm (m : Measurement ι S) (V : Evolution S)
    (W : ι → Evolution S) (e : ι ≃ ι)
    (hcomm : ∀ i, (m.op i).comp V.op = (W i).op.comp (m.op (e i))) (ρ : State S) (i : ι) :
    m.bornProb (V.evolve ρ) i = m.bornProb ρ (e i) := by
  rw [bornProb_eq_re_trace_postOp, bornProb_eq_re_trace_postOp,
    trace_postOp_evolve_of_reindex_comm m V W e hcomm ρ i]

end Measurement

end AxQM
