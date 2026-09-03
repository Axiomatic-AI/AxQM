/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BellReducedState

/-!
# Nielsen & Chuang, Exercise 2.75 (reduced density operators of the Bell states)

*(N&C p. 106.)*

For each Bell state, find the reduced density operator for each qubit.

* `bellState_reducedLeft` — `Tr_B|β_xy⟩⟨β_xy| = I/2` (reduced density operator of the first qubit is
  maximally mixed), for all `x, y`.
* `bellState_reducedRight` — `Tr_A|β_xy⟩⟨β_xy| = I/2` (reduced density operator of the second qubit
  is maximally mixed), for all `x, y`.
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.75 (first qubit).** The reduced density operator of the first
qubit of any Bell state `|β_xy⟩` is the maximally mixed state `I/2`: `Tr_B|β_xy⟩⟨β_xy| =
maximallyMixedState qubit`, for all `x, y`. -/
theorem bellState_reducedLeft (x y : Fin 2) :
    (bellState x y).toState.reducedLeft = maximallyMixedState qubit := sorry

/-- **Nielsen & Chuang, Exercise 2.75 (second qubit).** The reduced density operator of the second
qubit of any Bell state `|β_xy⟩` is the maximally mixed state `I/2`: `Tr_A|β_xy⟩⟨β_xy| =
maximallyMixedState qubit`, for all `x, y`. -/
theorem bellState_reducedRight (x y : Fin 2) :
    (bellState x y).toState.reducedRight = maximallyMixedState qubit := sorry

end AxQM
