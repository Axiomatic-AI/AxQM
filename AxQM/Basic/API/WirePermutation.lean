/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution
import AxQM.Basic.PiTensor
import AxQM.Basic.PiTensorState

/-!
# AxQM.Basic.API — permuting the wires of an `n`-fold register

The operator-level form of an arbitrary permutation of the wires of an `n`-qubit (more generally
`n`-copy) register `S ^⊗ₛ n`, realised as a genuine closed-system `Evolution`. This is the
general-`n` **SWAP-network primitive**: the two-factor `Evolution.swap` is the `n = 2`
transposition, and here every wire permutation `σ : Equiv.Perm (Fin n)` becomes a unitary
`Evolution.permWires σ` on the register.

## Main declarations
* `Evolution.permWires σ` — the **wire-permutation gate** on `S ^⊗ₛ n`: the closed-system
  `Evolution` that relabels the tensor factors by `σ`. It is `Evolution.ofLinearIsometryEquiv` of
  the factor-reindexing isometry `PiTensorProduct.reindexₗᵢ` along `σ`, so it is in the
  `Evolution` primitive with unitarity inherited from that isometry — the same
  construction pattern as `Evolution.swap`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem} {n : ℕ}

/-- **The wire-permutation gate** on the `n`-fold register `S ^⊗ₛ n`: given a permutation `σ :
Equiv.Perm (Fin n)` of the wires, the closed-system `Evolution` that relabels the tensor factors
by `σ`. -/
def Evolution.permWires (σ : Equiv.Perm (Fin n)) : Evolution (S ^⊗ₛ n) :=
  Evolution.ofLinearIsometryEquiv (PiTensorProduct.reindexₗᵢ ℂ (fun _ : Fin n => S.space) σ)

end AxQM
