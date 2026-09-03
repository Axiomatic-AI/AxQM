/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledNotBasis
import AxQM.Basic.API.ControlledControlledUnitary

/-!
# Placing a single-qubit gate on one wire of the control tower (N&C Problem 5.2)

The Figure 5.1 QFT circuit, read on the `(n+1)`-qubit control tower `qtower n qubit`, contains
**Hadamards** — single-qubit gates acting on *one wire*. This file supplies the wire-addressed
placement of a single-qubit gate on the tower.

## Main declarations
* `Evolution.qtowerSingleWire n i g` — the **single-wire gate**: the single-qubit `Evolution` `g`
  placed on wire `i` of `qtower n qubit`, the identity on every other wire. Defined by recursion on
  the tower: on the head wire (`i = 0`) it is `g.onLeft` (`g ⊗ 1`), and on a later wire (`i = i'+1`)
  it wraps the placement on the tail with an idle head, `(qtowerSingleWire i' g).onRight qubit`
  (`1 ⊗ ⋯`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **A single-qubit gate placed on one wire of the control tower** `qtower n qubit`: the gate `g`
acts on wire `i`, the identity on every other wire. Defined by recursion on the tower — on the head
wire (`i = 0`) it is `g.onLeft (qtower n qubit)` (`g ⊗ 1`), and on a later wire (`i = i'+1`) it
wraps the placement on the tail with an idle head,
`(Evolution.qtowerSingleWire n i' g).onRight qubit`
(`1 ⊗ ⋯`). This is the shape of the Figure 5.1 Hadamards. -/
def Evolution.qtowerSingleWire :
    (n : ℕ) → Fin (n + 1) → Evolution qubit → Evolution (qtower n qubit)
  | 0, _, g => g
  | n + 1, i, g =>
      Fin.cases (g.onLeft (qtower n qubit))
        (fun i' => (Evolution.qtowerSingleWire n i' g).onRight qubit) i

end AxQM
