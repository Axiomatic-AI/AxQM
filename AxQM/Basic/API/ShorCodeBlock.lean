/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BitFlipSyndromeMeasurement
import AxQM.Basic.API.Eigenstate

/-!
# AxQM.Basic.API — the Shor-code blocks and their sign-readout observable

Infrastructure for the phase-flip layer of the nine-qubit Shor code (Nielsen &
Chuang §10.2, Exercise 10.5). The Shor code is a *concatenation*: each of the three "phase-flip
qubits" `|±⟩` is encoded by the three-qubit bit-flip code into a **block** of three physical
qubits.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **`X ⊗ X ⊗ X`**, the block **sign-readout observable** on the three-qubit register
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`: the product of the three Pauli `X`s of the block. Its `±1`
eigenvalue on a cat state reads off that block's `+`/`−` sign (`X⊗X⊗X (|000⟩ ± |111⟩) = ±(|000⟩ ±
|111⟩)`), so measuring it compares — for a pair of blocks, via the product `X⊗X⊗X ⊗ X⊗X⊗X` — the
signs of the two blocks. This is the per-block ingredient of the Shor phase-flip syndrome
observables. -/
def blockXObservable : Observable bitFlipReg :=
  pauliXObservable ⊗ (pauliXObservable ⊗ pauliXObservable)

/-- The **unnormalised block cat vector** `|000⟩ + (−1)^σ |111⟩` on `bitFlipReg`: `σ = 0` gives
`|000⟩ + |111⟩` (the bit-flip encoding of `|+⟩`) and `σ = 1` gives `|000⟩ − |111⟩` (the encoding of
`|−⟩`). -/
def catBlockVec (σ : Fin 2) : bitFlipReg.space :=
  (qubitThreeBasis (0, 0, 0)).vec + (-1 : ℂ) ^ (σ : ℕ) • (qubitThreeBasis (1, 1, 1)).vec

/-- The cat vector is nonzero. -/
theorem catBlockVec_ne_zero (σ : Fin 2) : catBlockVec σ ≠ 0 := by
  intro h
  have hi : inner ℂ (qubitThreeBasis (0, 0, 0)).vec (catBlockVec σ) = 0 := by
    rw [h, inner_zero_right]
  rw [catBlockVec, inner_add_right, inner_smul_right,
    orthonormal_iff_ite.mp qubitThreeBasis_orthonormal (0, 0, 0) (0, 0, 0),
    orthonormal_iff_ite.mp qubitThreeBasis_orthonormal (0, 0, 0) (1, 1, 1)] at hi
  simp at hi

/-- The **normalised block cat state** `(|000⟩ + (−1)^σ |111⟩)/√2`, the sign-`(−1)^σ` eigenstate of
the block. -/
def catBlockState (σ : Fin 2) : PureState bitFlipReg :=
  PureState.normalize (catBlockVec σ) (catBlockVec_ne_zero σ)

end AxQM
