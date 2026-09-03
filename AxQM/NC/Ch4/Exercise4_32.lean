/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.UnreadMeasurement
import AxQM.Basic.API.CompositeMeasurement
import AxQM.Basic.PartialTrace
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# Nielsen & Chuang, Exercise 4.32 (unread measurement; no-signalling)

*(N&C p. 187.)*

Show unread measurement gives rho'=P0 rho P0+P1 rho P1 and preserves tr_2.

* `unreadState_reducedLeft_onRight`
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S T : QSystem}

namespace Measurement

/-- **Nielsen–Chuang Exercise 4.32, Claim 2 (the reduced state is preserved; no-signalling).**
Measuring the second (right) factor of a bipartite system `S ⊗ T` by an *unread* (non-selective)
measurement leaves the reduced density matrix of the first (left) factor unchanged:
`tr₂(ρ) = tr₂(ρ')`, i.e. `(ρ').reducedLeft = ρ.reducedLeft` where `ρ' = (m.onRight S).unreadState ρ`
has operator `Σᵢ (1 ⊗ Mᵢ) ρ (1 ⊗ Mᵢ†)`.
-/
theorem unreadState_reducedLeft_onRight (m : Measurement ι T) (ρ : State (S ⊗ T)) :
    ((m.onRight S).unreadState ρ).reducedLeft = ρ.reducedLeft := sorry

end Measurement

end AxQM
