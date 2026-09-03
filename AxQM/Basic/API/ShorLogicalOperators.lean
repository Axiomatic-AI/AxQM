/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorStabilizer
import AxQM.Basic.API.ShorCodePhaseFlip

/-!
# AxQM.Basic.API — the Shor-code logical operators `Z̄`, `X̄` and their algebra

Infrastructure for Nielsen & Chuang **Exercise 10.48** (§10.5.6, Figure 10.11): the
logical operators `Z̄ = X₁X₂…X₉` and `X̄ = Z₁Z₂…Z₉` of the nine-qubit Shor code, and the
stabilizer-formalism content of the exercise — that each of `Z̄, X̄` **commutes with** the eight
generators of Figure 10.11 (so both lie in the normalizer of the stabilizer), that they are
**independent of** the stabilizer (they act non-trivially on the code space, which every stabilizer
element fixes), and that `X̄` **anticommutes with** `Z̄` (the logical Pauli algebra `X̄Z̄ = −Z̄X̄`).
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **The Shor logical-`Z` operator `Z̄ = X₁X₂…X₉`** of Figure 10.11: the product of the nine Pauli
`X`s, as `X⊗X⊗X` (`blockXObservable`) on each of the three blocks of `shorReg`. Packaged as an
`Observable` (it is Hermitian). -/
noncomputable def shorLogicalZBar : Observable shorReg :=
  blockXObservable.tmul (blockXObservable.tmul blockXObservable)

/-- **The Shor logical-`X` operator `X̄ = Z₁Z₂…Z₉`** of Figure 10.11: the product of the nine Pauli
`Z`s, as the block phase gate `Z⊗Z⊗Z` (`blockZGate`) on each of the three blocks of `shorReg`.
Packaged as a unitary `Evolution`. -/
noncomputable def shorLogicalXBar : Evolution shorReg :=
  blockZGate.tmul (blockZGate.tmul blockZGate)

/-- **`Z̄` commutes with `g₁ = Z₁Z₂`** (`shorZ12`). -/
theorem shorLogicalZBar_op_comm_shorZ12 :
    shorLogicalZBar.op * shorZ12.op = shorZ12.op * shorLogicalZBar.op := sorry

/-- **`Z̄` commutes with `g₂ = Z₂Z₃`** (`shorZ23`). -/
theorem shorLogicalZBar_op_comm_shorZ23 :
    shorLogicalZBar.op * shorZ23.op = shorZ23.op * shorLogicalZBar.op := sorry

/-- **`Z̄` commutes with `g₃ = Z₄Z₅`** (`shorZ45`). -/
theorem shorLogicalZBar_op_comm_shorZ45 :
    shorLogicalZBar.op * shorZ45.op = shorZ45.op * shorLogicalZBar.op := sorry

/-- **`Z̄` commutes with `g₄ = Z₅Z₆`** (`shorZ56`). -/
theorem shorLogicalZBar_op_comm_shorZ56 :
    shorLogicalZBar.op * shorZ56.op = shorZ56.op * shorLogicalZBar.op := sorry

/-- **`Z̄` commutes with `g₅ = Z₇Z₈`** (`shorZ78`). -/
theorem shorLogicalZBar_op_comm_shorZ78 :
    shorLogicalZBar.op * shorZ78.op = shorZ78.op * shorLogicalZBar.op := sorry

/-- **`Z̄` commutes with `g₆ = Z₈Z₉`** (`shorZ89`). -/
theorem shorLogicalZBar_op_comm_shorZ89 :
    shorLogicalZBar.op * shorZ89.op = shorZ89.op * shorLogicalZBar.op := sorry

/-- **`Z̄` commutes with `g₇ = X₁X₂X₃X₄X₅X₆`** (`shorPhaseSyndromeX123456`). -/
theorem shorLogicalZBar_op_comm_shorPhaseSyndromeX123456 :
    shorLogicalZBar.op * shorPhaseSyndromeX123456.op
      = shorPhaseSyndromeX123456.op * shorLogicalZBar.op := sorry

/-- **`Z̄` commutes with `g₈ = X₄X₅X₆X₇X₈X₉`** (`shorPhaseSyndromeX456789`). -/
theorem shorLogicalZBar_op_comm_shorPhaseSyndromeX456789 :
    shorLogicalZBar.op * shorPhaseSyndromeX456789.op
      = shorPhaseSyndromeX456789.op * shorLogicalZBar.op := sorry

/-- **`X̄` commutes with `g₁ = Z₁Z₂`** (`shorZ12`). -/
theorem shorLogicalXBar_op_comm_shorZ12 :
    shorLogicalXBar.op * shorZ12.op = shorZ12.op * shorLogicalXBar.op := sorry

/-- **`X̄` commutes with `g₂ = Z₂Z₃`** (`shorZ23`). -/
theorem shorLogicalXBar_op_comm_shorZ23 :
    shorLogicalXBar.op * shorZ23.op = shorZ23.op * shorLogicalXBar.op := sorry

/-- **`X̄` commutes with `g₃ = Z₄Z₅`** (`shorZ45`). -/
theorem shorLogicalXBar_op_comm_shorZ45 :
    shorLogicalXBar.op * shorZ45.op = shorZ45.op * shorLogicalXBar.op := sorry

/-- **`X̄` commutes with `g₄ = Z₅Z₆`** (`shorZ56`). -/
theorem shorLogicalXBar_op_comm_shorZ56 :
    shorLogicalXBar.op * shorZ56.op = shorZ56.op * shorLogicalXBar.op := sorry

/-- **`X̄` commutes with `g₅ = Z₇Z₈`** (`shorZ78`). -/
theorem shorLogicalXBar_op_comm_shorZ78 :
    shorLogicalXBar.op * shorZ78.op = shorZ78.op * shorLogicalXBar.op := sorry

/-- **`X̄` commutes with `g₆ = Z₈Z₉`** (`shorZ89`). -/
theorem shorLogicalXBar_op_comm_shorZ89 :
    shorLogicalXBar.op * shorZ89.op = shorZ89.op * shorLogicalXBar.op := sorry

/-- **`X̄` commutes with `g₇ = X₁X₂X₃X₄X₅X₆`** (`shorPhaseSyndromeX123456`). -/
theorem shorLogicalXBar_op_comm_shorPhaseSyndromeX123456 :
    shorLogicalXBar.op * shorPhaseSyndromeX123456.op
      = shorPhaseSyndromeX123456.op * shorLogicalXBar.op := sorry

/-- **`X̄` commutes with `g₈ = X₄X₅X₆X₇X₈X₉`** (`shorPhaseSyndromeX456789`). -/
theorem shorLogicalXBar_op_comm_shorPhaseSyndromeX456789 :
    shorLogicalXBar.op * shorPhaseSyndromeX456789.op
      = shorPhaseSyndromeX456789.op * shorLogicalXBar.op := sorry

/-- **`X̄` anticommutes with `Z̄`:** `X̄ Z̄ = −Z̄ X̄`. This is the logical Pauli anticommutation
that makes `Z̄, X̄` a genuine logical `Z, X` pair. -/
theorem shorLogicalXBar_op_anticomm_shorLogicalZBar_op :
    shorLogicalXBar.op * shorLogicalZBar.op = -(shorLogicalZBar.op * shorLogicalXBar.op) := sorry

end AxQM
