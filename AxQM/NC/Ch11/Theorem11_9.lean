/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.UnreadMeasurement
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.RelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedKleinInequality

/-!
# N&C Theorem 11.9 — Projective measurements increase entropy

*(N&C p. 515.)*

Projective measurements increase entropy: S(rho')>=S(rho), equality iff rho=rho'.

* `vonNeumannEntropy_unreadState_ge` — `S(ρ) ≤ S(ρ')` (eq. (11.66)).
* `vonNeumannEntropy_unreadState_eq_iff` — `S(ρ') = S(ρ) ↔ ρ' = ρ`, the equality condition.
-/

open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **Nielsen & Chuang Theorem 11.9, eq. (11.66): projective measurements never decrease entropy.**
For a projective measurement `m` and any state `ρ`, the unread (non-selective) post-measurement
state `ρ' = Σᵢ Pᵢ ρ Pᵢ` (`m.unreadState ρ`) has entropy at least that of `ρ`,

  `S(ρ) ≤ S(ρ')`.

In full N&C generality: no faithfulness hypothesis on `ρ`. -/
theorem Measurement.IsProjective.vonNeumannEntropy_unreadState_ge {m : Measurement ι S}
    (h : m.IsProjective) (ρ : State S) :
    ρ.vonNeumannEntropy ≤ (m.unreadState ρ).vonNeumannEntropy := sorry

/-- **Nielsen & Chuang Theorem 11.9, equality condition.** For a projective measurement `m` and any
state `ρ`, the unread post-measurement state `ρ' = Σᵢ Pᵢ ρ Pᵢ` (`m.unreadState ρ`) has the
*same* entropy as `ρ` if and only if the measurement leaves the state unchanged,

`S(ρ') = S(ρ) ↔ ρ' = ρ`.
-/
theorem Measurement.IsProjective.vonNeumannEntropy_unreadState_eq_iff {m : Measurement ι S}
    (h : m.IsProjective) (ρ : State S) :
    (m.unreadState ρ).vonNeumannEntropy = ρ.vonNeumannEntropy ↔ m.unreadState ρ = ρ := sorry

end AxQM
