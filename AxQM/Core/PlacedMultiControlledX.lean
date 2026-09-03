/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.TensorPowMultiControlledX
import AxQM.Basic.API.WirePermutation
import AxQM.Basic.API.Qubit
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import AxQM.Basic.API.WireGatePlacement

/-!
# Placing `Cᵏ(X)` on a chosen set of wires (N&C Exercise 4.29, evolution-realization brick 8)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The recursive Barenco construction (Exercise
4.30's `barencoNCircuit`, and the classical halving circuit)
bottoms out into a sequence of multiply-controlled `NOT` blocks `Cᵏ(X)` (`k ≤ 2` are exactly the
`Toffoli`/`CNOT`/`NOT` gates), **each acting on a chosen, non-contiguous set of `k + 1` wires** of
the register. Turning such a block into a genuine closed-system `Evolution` is the last placement
primitive the assembly needs.

## Main declarations
* `Evolution.placedMcCtrlX k b σ` — the `Cᵏ(X)` gate (`k` controls, one target = `k + 1` wires)
  placed on the `(k+1)`-wire set `σ 0, …, σ k` of the `(k+1+b)`-wire register `qubit ^⊗ₛ (k+1+b)`,
  built as `(Evolution.tensorPowMcCtrlX k).onWires b σ`. A genuine closed-system `Evolution` on the
  whole register — no work qubit beyond the `b` ambient wires it acts on as identity.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **`Cᵏ(X)` placed on a chosen set of wires.** Given a wire permutation
`σ : Equiv.Perm (Fin (k + 1 + b))`, the multiply-controlled `NOT` `Cᵏ(X)` (`k` controls, one target,
so `k + 1` wires) placed on the wire set `σ 0, …, σ k` of the `(k+1+b)`-wire register
`qubit ^⊗ₛ (k+1+b)`, built by placing the symmetric-register `Cᵏ(X)` gate
`Evolution.tensorPowMcCtrlX k` (brick 7) via the arbitrary-wire combinator `Evolution.onWires`
(brick 6). A genuine closed-system `Evolution` acting as `Cᵏ(X)` on its `k + 1` target wires and as
the identity on the other `b`. For `k ≤ 2` this is a `Toffoli`/`CNOT`/`NOT` addressed to arbitrary
wires. -/
def Evolution.placedMcCtrlX (k b : ℕ) (σ : Equiv.Perm (Fin (k + 1 + b))) :
    Evolution (qubit ^⊗ₛ (k + 1 + b)) :=
  (Evolution.tensorPowMcCtrlX k).onWires b σ

end AxQM
