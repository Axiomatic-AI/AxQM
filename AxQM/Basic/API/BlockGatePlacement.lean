/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.TensorPowSplit
import AxQM.Basic.API.LeftPairGate
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.PiTensorState

/-!
# Placing a gate on a contiguous block of wires (N&C Exercise 4.29, evolution-realization brick 5b)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit implementing
`Cⁿ(X)`. Bottoming the multiply-controlled-`NOT` blocks `Cᵏ(X)` of the tight `(n+1)`-wire circuit to
genuine two-control gates requires placing a `Toffoli`/`CNOT` on a chosen set of wires. This is
done in two moves on the **symmetric** register
`S ^⊗ₛ (a+b)`: first place the gate on the *first* `a` wires (a contiguous block), then relabel the
wires by a permutation (`Evolution.permWires`, brick 1) to send that block to the target wire set.
This brick supplies the first move.

## Main declarations
* `Evolution.onBlock G b` — the **block-placement gate** on `S ^⊗ₛ (a+b)`: given a gate
  `G : Evolution (S ^⊗ₛ a)` on the first `a` wires, the closed-system `Evolution` acting as `G` on
  those wires and as the identity on the remaining `b`, defined as `G.onLeft (S ^⊗ₛ b)` transported
  across `(QSystem.tensorPowAdd S a b).symm` via `Evolution.congr`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem} {a : ℕ}

/-- **The block-placement gate** on `S ^⊗ₛ (a+b)`: given a gate `G : Evolution (S ^⊗ₛ a)` on the
first `a` wires, the closed-system `Evolution` that acts as `G` on those `a` wires and as the
identity on the remaining `b`. -/
def Evolution.onBlock (G : Evolution (S ^⊗ₛ a)) (b : ℕ) : Evolution (S ^⊗ₛ (a + b)) :=
  (G.onLeft (S ^⊗ₛ b)).congr (QSystem.tensorPowAdd S a b).symm

end AxQM
