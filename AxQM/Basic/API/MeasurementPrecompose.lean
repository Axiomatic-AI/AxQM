/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CompositeMeasurement

/-!
# AxQM — pre-composing a measurement with a unitary

A unitary applied just before a measurement can be absorbed into the measurement itself.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- **Pre-composing a measurement by a unitary** `U`: the measurement whose operators are
`Mᵢ U`. -/
def precompose (m : Measurement ι S) (U : Evolution S) : Measurement ι S where
  op i := (m.op i).comp U.op
  complete := by
    have key : ∀ i, (adjoint ((m.op i).comp U.op)).comp ((m.op i).comp U.op)
        = (adjoint U.op).comp (((adjoint (m.op i)).comp (m.op i)).comp U.op) := by
      intro i
      rw [ContinuousLinearMap.adjoint_comp]
      simp only [ContinuousLinearMap.comp_assoc]
    rw [Finset.sum_congr rfl fun i _ => key i, ← ContinuousLinearMap.comp_finset_sum,
      ← ContinuousLinearMap.finset_sum_comp, m.complete]
    simp only [← ContinuousLinearMap.mul_def, one_mul]
    rw [ContinuousLinearMap.mul_def]
    exact U.adjoint_comp_self

end Measurement

end AxQM
