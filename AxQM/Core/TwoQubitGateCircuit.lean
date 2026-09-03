/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ControlPairGates

/-!
# A two-qubit-gate-count model for three-qubit circuits (Nielsen & Chuang §4.3)

Nielsen & Chuang **Exercise 4.25** (Fredkin gate construction) closes with two *gate-count* claims
phrased over **two-qubit gates**: part (3) builds the Fredkin gate "using only **six two-qubit
gates**", and part (4) asks for an even simpler construction with "only **five two-qubit gates**".
Here a *controlled single-qubit gate* `C(V)` counts as **one** two-qubit gate — the same convention
that makes Figure 4.8's `C²(U)` decomposition "five two-qubit gates" (`C(V)`, `CNOT`, `C(V†)`,
`CNOT`, `C(V)`). To state such a claim *faithfully* the count must be a genuine proposition about a
circuit, not a term the reader tallies by eye.

## Main declarations
* `TwoQubitGate3` — a two-qubit gate on `qubit ⊗ (qubit ⊗ qubit)`, in one of four forms. The
  parts-1–3 forms `pair`/`ctrl` are chosen so the placements those parts need are bare composites
  with no associator/SWAP bookkeeping (the placements in `ccontrolledUnitaryCircuit`, Exercise
  4.21); the part-4 forms `pairAB`/`pairAC` add an arbitrary gate on a *control* pair via
  associator/`leftComm` transport:
  * `pair U` — an **arbitrary** two-qubit gate `U : Evolution (qubit ⊗ qubit)` on the target pair
    `{1, 2}`, with the control wire `0` idle (`U.onRight qubit = 1 ⊗ U`);
  * `ctrl t g` — a **control-wire-`0`** gate: the single-qubit gate `g` on wire `1` (`t = 0`) or
    wire `2` (`t = 1`), conditioned on wire `0`, with the remaining wire idle
    (`controlledUnitary (g.onLeft/onRight qubit)`).
  * `pairAB U` / `pairAC U` — an **arbitrary** two-qubit gate `U` on a *control* pair, `{0,1}`
    (`leftPairGate U`, wire `2` idle) or `{0,2}` (`outerPairGate U`, wire `1` idle). Unlike `ctrl`
    these admit *entangling* gates on a control pair — the class Exercise 4.25 part 4's
    five-two-qubit-gate Fredkin construction provably needs (a controlled-single-qubit alphabet
    cannot reach five gates). Parts 1–3 use only `pair`/`ctrl`; these extend the *same* count model
    so "five two-qubit gates" is compared like-for-like with part 3's "six".
* `twoQubitCircuit gs = (gs.map TwoQubitGate3.denote).prod` — the composite `Evolution`, in operator
  order (leftmost gate is the leftmost `comp` factor, applied last).
* `twoQubitCount gs = gs.length` — the two-qubit-gate count.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **A two-qubit gate in a three-qubit circuit** on `qubit ⊗ (qubit ⊗ qubit)` (wires `0, 1, 2`),
in one of four genuine two-qubit forms:

* `pair U` — an arbitrary two-qubit gate `U` on the target pair `{1, 2}`, control wire `0` idle;
* `ctrl t g` — the single-qubit gate `g` on wire `1` (`t = 0`) or wire `2` (`t = 1`), controlled on
  wire `0`, the remaining wire idle;
* `pairAB U` — an arbitrary two-qubit gate `U` on the left control pair `{0, 1}` (via
  `leftPairGate`, wire `2` idle);
* `pairAC U` — an arbitrary two-qubit gate `U` on the outer control pair `{0, 2}` (via
  `outerPairGate`, wire `1` idle).

`pairAB`/`pairAC` admit *entangling* gates on a control pair — the class Exercise 4.25 part 4's
five-two-qubit-gate Fredkin construction needs, which `ctrl` (controlled-single-qubit) cannot give.
Its `TwoQubitGate3.denote`ation is an `Evolution`; because every gate is a two-qubit gate, the
number of two-qubit gates in a list is just its `twoQubitCount` (= length), so "the Fredkin gate is
built from at most `n` two-qubit gates" becomes a genuine proposition. -/
inductive TwoQubitGate3 where
  | /-- An arbitrary two-qubit gate `U` on the target pair `{1, 2}` (control wire `0` idle). -/
    pair (U : Evolution (qubit ⊗ qubit))
  | /-- The single-qubit gate `g` controlled on wire `0`, targeting wire `1` (`target = 0`) or
      wire `2` (`target = 1`). -/
    ctrl (target : Fin 2) (g : Evolution qubit)
  | /-- An arbitrary two-qubit gate `U` on the left control pair `{0, 1}` (wire `2` idle), placed
      via `leftPairGate`. Needed for the five-two-qubit-gate Fredkin construction (Exercise 4.25
      part 4), whose entangling gate on a control pair is not of `ctrl` (controlled-single-qubit)
      form. -/
    pairAB (U : Evolution (qubit ⊗ qubit))
  | /-- An arbitrary two-qubit gate `U` on the outer control pair `{0, 2}` (wire `1` idle), placed
      via `outerPairGate`. -/
    pairAC (U : Evolution (qubit ⊗ qubit))

namespace TwoQubitGate3

/-- **The `Evolution` denoted by a single two-qubit gate** (all four forms). -/
def denote : TwoQubitGate3 → Evolution (qubit ⊗ (qubit ⊗ qubit))
  | pair U => U.onRight qubit
  | ctrl 0 g => controlledUnitary (g.onLeft qubit)
  | ctrl _ g => controlledUnitary (g.onRight qubit)
  | pairAB U => leftPairGate U
  | pairAC U => outerPairGate U

end TwoQubitGate3

/-- **The evolution implemented by a two-qubit-gate list**. -/
def twoQubitCircuit (gs : List TwoQubitGate3) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (gs.map TwoQubitGate3.denote).prod

/-- **The number of two-qubit gates** in a two-qubit-gate circuit. Since every element of the list
is a two-qubit gate, this is simply the list length. -/
def twoQubitCount (gs : List TwoQubitGate3) : ℕ := gs.length

end AxQM
