/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QtowerTensorPow
import AxQM.Basic.API.LeftPairGate

/-!
# `Cⁿ(X)` on the symmetric tensor-power register (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of Toffoli,
`CNOT` and single-qubit gates implementing the `n`-controlled `NOT` `Cⁿ(X)`. This file carries that
gate onto the **symmetric** power `qubit ^⊗ₛ (n+1)` (the `n+1`-fold `PiTensorProduct`, where a wire
relabelling is a clean `reindexₗᵢ`).

## Main declarations
* `Evolution.tensorPowMcCtrlX n` — the **symmetric-register form of `Cⁿ(X)`**: the gate
  `mcCtrl n pauliXGate` transported onto `qubit ^⊗ₛ (n+1)` through the `qtower ↔ tensor-power`
  bridge `qtowerQubitTensorPow n`. A genuine closed-system `Evolution` on exactly the `(n+1)`-wire
  register — no work qubit — equal to `Cⁿ(X)` up to the (isometric) change of register description.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **The multiply-controlled `NOT` `Cⁿ(X)` on the symmetric tensor-power register.** The
gate `mcCtrl n pauliXGate : Evolution (qtower n qubit)` transported onto the symmetric
`(n+1)`-fold power `qubit ^⊗ₛ (n+1)` through the `qtower ↔ tensor-power` bridge
`qtowerQubitTensorPow n` by `Evolution.congr`. It acts on exactly the `(n+1)`-wire
register — no work qubit — and equals `Cⁿ(X)` up to the isometric change of register
description. -/
def Evolution.tensorPowMcCtrlX (n : ℕ) : Evolution (qubit ^⊗ₛ (n + 1)) :=
  Evolution.congr (qtowerQubitTensorPow n) (mcCtrl n pauliXGate)

end AxQM
