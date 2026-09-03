/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CascadedMeasurement

/-!
# Relabelling the outcomes of a measurement

Given a measurement `m : Measurement ι S` and an equivalence `e : Y ≃ ι` between outcome sets, the
**outcome relabelling** `m.reindexOutcome e : Measurement Y S` is the same POVM read through `e`:
its operator at `y` is `m.op (e y)`.
-/

open ContinuousLinearMap InnerProductSpace
open scoped BigOperators

noncomputable section

namespace AxQM

namespace Measurement

variable {ι Y : Type*} [Fintype ι] [Fintype Y] {S : QSystem}

/-- **Relabelling the outcomes of a measurement.** For a measurement `m : Measurement ι S` and an
equivalence `e : Y ≃ ι` of outcome sets, `m.reindexOutcome e` is the measurement on `S` with
outcome set `Y` whose operator at `y` is `m.op (e y)`. -/
def reindexOutcome (m : Measurement ι S) (e : Y ≃ ι) : Measurement Y S where
  op y := m.op (e y)
  complete := by
    rw [Equiv.sum_comp e fun i => (adjoint (m.op i)).comp (m.op i)]
    exact m.complete

end Measurement

end AxQM
