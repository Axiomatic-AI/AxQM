/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.PiTensorState
import AxQM.Basic.API.PseudoInverse
import AxQM.ToMathlib.Analysis.InnerProductSpace.PiTensorProduct

/-!
# AxQM.Basic.API — the `n`-fold tensor-power state `ρ^⊗n` and its spectrum

The **`n`-fold tensor power** of a quantum state `ρ : State S` is the product state
`ρ^⊗n = ρ ⊗ ⋯ ⊗ ρ` (`n` factors) living on the tensor-power system `S ^⊗ₛ n`. Because
`S ^⊗ₛ n` is definitionally the indexed composite `⨂ₛ _ : Fin n, S`
and the indexed product state `⨂ₚ i, ρ i` is already available
(`State.piTensor`), the tensor power is simply
`State.piTensor` over the *constant* family `fun _ : Fin n ↦ ρ`. It inherits its
density-operator status for free.

## Main definitions and results

* `AxQM.State.tensorPow` (`ρ^⊗n`) — the `n`-fold tensor-power state, on `S ^⊗ₛ n`.
* `AxQM.State.tensorPowEigenbasis` — the product eigenbasis
  `⨂ᵢ |e_{κᵢ}⟩` of `ρ^⊗n`, an orthonormal basis of `(S ^⊗ₛ n).space` indexed by
  `Fin n → Fin d`.
-/

open scoped InnerProductSpace TensorProduct BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The **`n`-fold tensor-power state** `ρ^⊗n` of a quantum state `ρ : State S`, living on the
tensor-power system `S ^⊗ₛ n`. It is the indexed product state `⨂ₚ _ : Fin n, ρ`
(`State.piTensor` over the constant family), the `n`-ary analogue of the binary product state
`ρ ⊗ σ` (`State.tmul`); a genuine `State` because the `n`-ary tensor of density operators is a
density operator. -/
def State.tensorPow (ρ : State S) (n : ℕ) : State (S ^⊗ₛ n) := ⨂ₚ _ : Fin n, ρ

/-- The **product eigenbasis** of `ρ^⊗n`: the `n`-ary tensor `⨂ᵢ |e_{κᵢ}⟩` of `ρ`'s spectral
eigenbasis `e = ρ.isDensity.isSymmetric.eigenvectorBasis` (`OrthonormalBasis.piTensorProduct`),
an orthonormal basis of `(S ^⊗ₛ n).space` indexed by the length-`n` sequences `κ : Fin n → Fin
(dim S.space)`. -/
def State.tensorPowEigenbasis (ρ : State S) (n : ℕ) :
    OrthonormalBasis (Fin n → Fin (Module.finrank ℂ S.space)) ℂ (S ^⊗ₛ n).space :=
  OrthonormalBasis.piTensorProduct fun _ : Fin n => ρ.isDensity.isSymmetric.eigenvectorBasis rfl

end AxQM
