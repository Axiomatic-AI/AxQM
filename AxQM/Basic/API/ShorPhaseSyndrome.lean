/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorCodeBlock

/-!
# AxQM.Basic.API — the Shor-code phase-flip syndrome observables

Infrastructure for the phase-flip layer of the nine-qubit Shor code (Nielsen &
Chuang §10.2, Exercise 10.5). The Shor code is a *concatenation*: three "phase-flip qubits" `|±⟩`,
each encoded by the three-qubit bit-flip code into a **block** — the cat state
`catBlockState σ = (|000⟩ + (−1)^σ |111⟩)/√2`. Detecting a phase flip means *comparing the signs
of adjacent blocks*, just as the bare phase-flip code compares the signs of adjacent qubits by
measuring `X₁X₂`, `X₂X₃`.
This file assembles the nine-qubit register and the two block-sign-comparison observables.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **The nine-qubit Shor register** `bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)`: three copies of the
three-qubit bit-flip register, one per "phase-flip qubit" of the concatenated Shor code (N&C §10.2).
Its physical qubits are grouped into three blocks `(q₁q₂q₃)(q₄q₅q₆)(q₇q₈q₉)`. -/
abbrev shorReg : QSystem := bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)

/-- **`X₁X₂X₃X₄X₅X₆`**, the first Shor phase-flip syndrome observable: `X⊗X⊗X` on block 1, `X⊗X⊗X`
on block 2, identity on block 3. Its `±1` outcome compares the signs of the first two cat
blocks. -/
def shorPhaseSyndromeX123456 : Observable shorReg :=
  blockXObservable ⊗ (blockXObservable ⊗ Observable.id bitFlipReg)

/-- **`X₄X₅X₆X₇X₈X₉`**, the second Shor phase-flip syndrome observable: identity on block 1,
`X⊗X⊗X` on block 2, `X⊗X⊗X` on block 3. Its `±1` outcome compares the signs of the last two cat
blocks. -/
def shorPhaseSyndromeX456789 : Observable shorReg :=
  Observable.id bitFlipReg ⊗ (blockXObservable ⊗ blockXObservable)

/-- **A three-block product of sign-definite cat states** `catBlockState σ₁ ⊗ (catBlockState σ₂ ⊗
catBlockState σ₃)` on the nine-qubit register. The Shor logical codewords are the equal-sign
products `σ₁ = σ₂ = σ₃` (`|0_L⟩` at `0,0,0`, `|1_L⟩` at `1,1,1`); a phase flip on block `b` flips
`σ_b`, so the general product is exactly the family of states the phase-flip syndrome discriminates.
-/
def shorCatProduct (σ₁ σ₂ σ₃ : Fin 2) : PureState shorReg :=
  catBlockState σ₁ ⊗ (catBlockState σ₂ ⊗ catBlockState σ₃)

end AxQM
