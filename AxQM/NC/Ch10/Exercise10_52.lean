/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Exercise10_32

/-!
# Nielsen & Chuang, Exercise 10.52 — the Steane-code logical operators `Z̄`, `X̄`

*(N&C p. 470.)*

Verify by direct operation on codewords that (10.107) operators act as logical Z and X.

* `steaneLogicalZBar`, `steaneLogicalXBar` — the operators `Z̄ = Z^{𝟙}` and `X̄ = X^{𝟙}` of
  (10.107).
* `steaneLogicalZBar_hasEigenstate_logicalZero`, `steaneLogicalZBar_hasEigenstate_logicalOne` —
  `Z̄` acts as logical `Z`: `Z̄|0_L⟩ = |0_L⟩` and `Z̄|1_L⟩ = −|1_L⟩`.
* `steaneLogicalXBar_evolvePure_logicalZero`, `steaneLogicalXBar_evolvePure_logicalOne` — `X̄` acts
  as logical `X`: `X̄|0_L⟩ = |1_L⟩` and `X̄|1_L⟩ = |0_L⟩`.
-/

namespace AxQM

open AxQM.Concrete

open scoped Matrix

/-- **The Steane logical-`Z` operator `Z̄ = Z₁Z₂Z₃Z₄Z₅Z₆Z₇`** of Nielsen & Chuang eq. (10.107): the
uniform phase-flip Pauli string `Z^{𝟙}` on the seven-qubit register (`phaseString` at the all-ones
support word `𝟙`), as a unitary `Evolution`. -/
noncomputable def steaneLogicalZBar : Evolution (bitReg (Fin 7)) :=
  phaseString 1

/-- **The Steane logical-`X` operator `X̄ = X₁X₂X₃X₄X₅X₆X₇`** of Nielsen & Chuang eq. (10.107): the
uniform bit-flip Pauli string `X^{𝟙}` on the seven-qubit register (`bitString` at the all-ones
support word `𝟙`), as a unitary `Evolution`. -/
noncomputable def steaneLogicalXBar : Evolution (bitReg (Fin 7)) :=
  bitString 1

/-- **Nielsen & Chuang, Exercise 10.52 (`Z̄` fixes `|0_L⟩`).** The logical-`Z` operator
`Z̄ = Z₁…Z₇` acts as `+1` on the Steane logical zero, `Z̄|0_L⟩ = |0_L⟩`. This is the logical
`Z|0⟩ = |0⟩`. -/
theorem steaneLogicalZBar_hasEigenstate_logicalZero :
    steaneLogicalZBar.HasEigenstate 1 steaneLogicalZero := by
  have h := phaseString_hasEigenstate_cssStdState steaneDualCode
    (u := (1 : Fin 7 → ZMod 2)) (x := 0) (fun y hy => steaneDualCode_dotProduct_one hy)
  simpa only [dotProduct_zero, ZMod.val_zero, pow_zero] using h

/-- **Nielsen & Chuang, Exercise 10.52 (`Z̄` negates `|1_L⟩`).** The logical-`Z` operator
`Z̄ = Z₁…Z₇` acts as `−1` on the Steane logical one, `Z̄|1_L⟩ = −|1_L⟩`. This is the logical
`Z|1⟩ = −|1⟩`. -/
theorem steaneLogicalZBar_hasEigenstate_logicalOne :
    steaneLogicalZBar.HasEigenstate (-1) steaneLogicalOne := by
  have h := phaseString_hasEigenstate_cssStdState steaneDualCode
    (u := (1 : Fin 7 → ZMod 2)) (x := 1) (fun y hy => steaneDualCode_dotProduct_one hy)
  have hval : ((1 : Fin 7 → ZMod 2) ⬝ᵥ (1 : Fin 7 → ZMod 2)).val = 1 := by decide
  rw [hval, pow_one] at h
  exact h

/-- **Nielsen & Chuang, Exercise 10.52 (`X̄` maps `|0_L⟩` to `|1_L⟩`).** The logical-`X` operator
`X̄ = X₁…X₇` sends the Steane logical zero to the logical one, `X̄|0_L⟩ = |1_L⟩`. This is the
logical `X|0⟩ = |1⟩`. -/
theorem steaneLogicalXBar_evolvePure_logicalZero :
    steaneLogicalXBar.evolvePure steaneLogicalZero = steaneLogicalOne := sorry

/-- **Nielsen & Chuang, Exercise 10.52 (`X̄` maps `|1_L⟩` to `|0_L⟩`).** The logical-`X` operator
`X̄ = X₁…X₇` sends the Steane logical one back to the logical zero, `X̄|1_L⟩ = |0_L⟩`. This is the
logical `X|1⟩ = |0⟩`. -/
theorem steaneLogicalXBar_evolvePure_logicalOne :
    steaneLogicalXBar.evolvePure steaneLogicalOne = steaneLogicalZero := sorry

end AxQM
