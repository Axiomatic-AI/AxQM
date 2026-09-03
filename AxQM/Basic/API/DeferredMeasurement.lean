/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Measurement
import AxQM.Basic.Evolution
import AxQM.Basic.API.DeferredMeasurementReindex

/-!
# AxQM — deferring a gate past a measurement

Nielsen & Chuang's **principle of deferred measurement**: a unitary applied *before* a measurement
can be commuted to *after* it whenever the gate commutes with each measurement operator up to an
outcome-dependent unitary on the post-measurement branch.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- **Outcome probabilities are unchanged when the gate is deferred**: under the
commutation `Mᵢ V = Wᵢ Mᵢ`, the Born probability of outcome `i` on the evolved state `V ρ V†` equals
that on `ρ`, `p(i ∣ V ρ V†) = p(i ∣ ρ)`. The measurement statistics do not see the gate `V`. -/
theorem bornProb_evolve_of_comm (m : Measurement ι S) (V : Evolution S) (W : ι → Evolution S)
    (hcomm : ∀ i, (m.op i).comp V.op = (W i).op.comp (m.op i)) (ρ : State S) (i : ι) :
    m.bornProb (V.evolve ρ) i = m.bornProb ρ i :=
  bornProb_evolve_of_reindex_comm m V W (Equiv.refl ι) hcomm ρ i

end Measurement

end AxQM
