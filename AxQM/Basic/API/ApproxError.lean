/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Evolution
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# AxQM.Basic.API — the gate-approximation error `E(U,V)`

Nielsen & Chuang's *error* measure for approximating one unitary operation by another (Box 4.1,
"Approximating quantum circuits", page 195; N&C eq. 4.61), for a target evolution `U` and an
implemented `V`.

## Main declarations
* `Evolution.gateError` — `E(U,V) = ‖U.op - V.op‖`, N&C eq. 4.61.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The gate-approximation error** `E(U,V)`. -/
def Evolution.gateError (U V : Evolution S) : ℝ := ‖U.op - V.op‖

end AxQM
