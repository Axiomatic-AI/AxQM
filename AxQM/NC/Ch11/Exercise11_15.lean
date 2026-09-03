/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EntropyComposite
import AxQM.Basic.API.UnreadMeasurement
import AxQM.Basic.API.ResetMeasurement

/-!
# Nielsen & Chuang, Exercise 11.15 — a generalized measurement can decrease entropy

*(N&C p. 515.)*

Show a generalized measurement with given operators can decrease qubit entropy.

* `resetMeasurement_can_decrease_entropy` — `∃ ρ, S(ρ') < S(ρ)`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **N&C Exercise 11.15: the procedure can strictly decrease the entropy of the qubit.** There is a
state whose entropy is strictly greater than that of its unread post-measurement state. -/
theorem resetMeasurement_can_decrease_entropy :
    ∃ ρ : State qubit,
      (resetMeasurement.unreadState ρ).vonNeumannEntropy < ρ.vonNeumannEntropy := sorry

end AxQM
