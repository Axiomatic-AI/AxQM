/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.Evolution

/-!
# AxQM.Basic.API — control-branch extensionality and gate-algebra helpers

Machinery for **multiply-controlled** operations (Nielsen & Chuang §4.3), used to
reason about controlled gates on `qubit ⊗ R` for an *arbitrary* target system `R`. It generalises
the three-qubit tools of `ControlledControlledUnitary` from a fixed two-control system to an
arbitrary tail, so an `n`-control gate (`C(C(…C(U)…))`) can be handled one control at a time.

## Main declarations
* `Evolution.adjoint_comp_self'` — the gate-level unitarity cancellation `U† U = 1` (the
  `Evolution`-valued form of the op-level `Evolution.adjoint_comp_self`).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Uncompute cancellation** `U† U = 1` as an equality of `Evolution`s. -/
theorem Evolution.adjoint_comp_self' (U : Evolution S) : U.adjoint.comp U = Evolution.id := by
  apply Evolution.ext
  rw [Evolution.comp_op, Evolution.adjoint_op, Evolution.id_op, U.adjoint_comp_self]

end AxQM
