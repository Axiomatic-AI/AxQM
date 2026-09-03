/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BlockGatePlacement
import AxQM.Basic.API.WirePermutation
import AxQM.Basic.API.Qubit

/-!
# Placing a gate on an arbitrary set of wires (N&C Exercise 4.29, evolution-realization brick 6)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit implementing
`Cⁿ(X)`. Bottoming the multiply-controlled-`NOT` blocks of the tight `(n+1)`-wire circuit to
genuine two-control gates (`Toffoli`/`CNOT`/`NOT`) requires placing such a gate on a **chosen,
non-contiguous set of wires** of the register — the surgery both `Evolution.onBlock` (brick 5b) and
`Evolution.permWires` (brick 1) were built to enable. This brick assembles them into the general
arbitrary-wire placement gate.

## Main declarations
* `Evolution.onWires G b σ` — the **arbitrary-wire placement gate** on `S ^⊗ₛ (a+b)`: the gate `G`
  placed on the wires `σ 0, …, σ (a-1)`, built by conjugating `Evolution.onBlock G b` by
  `Evolution.permWires σ`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem} {a : ℕ}

/-- **The arbitrary-wire placement gate** on `S ^⊗ₛ (a+b)`: given a gate `G : Evolution (S ^⊗ₛ a)`
and a wire permutation `σ : Equiv.Perm (Fin (a+b))`, the closed-system `Evolution` that acts as `G`
on the wire set `σ 0, …, σ (a-1)` (the image of the front `a`-wire block under `σ`) and as the
identity on the remaining wires. It is the front-block gate `Evolution.onBlock G b` conjugated by
the wire permutation `Evolution.permWires σ` — relabel the target wires to the front, run `G`
there, then relabel back. -/
def Evolution.onWires (G : Evolution (S ^⊗ₛ a)) (b : ℕ) (σ : Equiv.Perm (Fin (a + b))) :
    Evolution (S ^⊗ₛ (a + b)) :=
  (Evolution.permWires σ).comp ((G.onBlock b).comp (Evolution.permWires σ.symm))

end AxQM
