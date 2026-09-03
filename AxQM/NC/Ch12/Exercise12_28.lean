/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.B92Protocol
import AxQM.Basic.API.PauliMeasurement
import AxQM.Basic.API.PauliEigen
import AxQM.Basic.API.EigenspaceCollapse
import AxQM.NC.Ch4.Exercise4_1

/-!
# Nielsen & Chuang, Exercise 12.28 (B92: `b = 1` forces perfect correlation of `a` and `a'`)

*(N&C p. 591.)*

B92: show when b=1, a and a' are perfectly correlated.

* `b92_perfectly_correlated` — the exercise: `P(b = 1 | a, a') ≠ 0 ↔ a ≠ a'`; observing `b = 1`
  happens exactly when `a` and `a'` differ, so `b = 1` pins them into perfect correlation.
-/

noncomputable section

namespace AxQM

/-- **Exercise 12.28.** When `b = 1`, the bits `a` and `a'` are **perfectly correlated**: the event
`b = 1` has positive Born probability exactly when `a ≠ a'`. Observing `b = 1` therefore certifies
`a ≠ a'` (equivalently `a' = 1 − a`), so each of Alice's and Bob's bits determines the other. -/
theorem b92_perfectly_correlated {a a' : Bool} : b92ProbB1 a a' ≠ 0 ↔ a ≠ a' := sorry

end AxQM
