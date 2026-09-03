/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CSSCode
import AxQM.Basic.API.CSSCodeStabilizer
import AxQM.Concrete.SteaneCode

/-!
# Nielsen & Chuang, Exercise 10.32 — the Fig 10.6 generators stabilize the Steane codewords

*(N&C p. 456.)*

Verify the six generators of Fig 10.6 stabilize the Steane code codewords.

* `steaneLogicalZero`
* `steaneLogicalOne`
* `steaneGenX`
* `steaneGenZ`
* `steaneStabilizer`
* `steaneStabilizer_hasEigenstate_one_logicalZero`
* `steaneStabilizer_hasEigenstate_one_logicalOne`
-/

namespace AxQM

open AxQM.Concrete

open scoped Matrix

/-- The **Steane logical zero** `|0_L⟩ = |0 + C₂⟩ = (1/√8) ∑_{y ∈ C₂} |y⟩` (Nielsen & Chuang, eq.
(10.78)), the standard CSS coset state over the dual Hamming code `C₂` at representative `0`. -/
noncomputable def steaneLogicalZero : PureState (bitReg (Fin 7)) :=
  cssStdState steaneDualCode 0

/-- The **Steane logical one** `|1_L⟩ = |𝟙 + C₂⟩ = (1/√8) ∑_{y ∈ C₂} |𝟙 + y⟩` (Nielsen & Chuang, eq.
(10.79)), the standard CSS coset state over `C₂` at the all-ones representative `𝟙 = 1111111`, an
element of `C₁ \ C₂`. -/
noncomputable def steaneLogicalOne : PureState (bitReg (Fin 7)) :=
  cssStdState steaneDualCode 1

/-- The three **X-type stabilizer generators** `g₁, g₂, g₃` of Figure 10.6: `steaneGenX i = X^{hᵢ}`
is the bit-flip Pauli string on the `i`-th row `hᵢ` of the Hamming parity-check matrix. -/
noncomputable def steaneGenX (i : Fin 3) : Evolution (bitReg (Fin 7)) :=
  bitString (hammingParityCheck i)

/-- The three **Z-type stabilizer generators** `g₄, g₅, g₆` of Figure 10.6: `steaneGenZ i = Z^{hᵢ}`
is the phase-flip Pauli string on the `i`-th row `hᵢ` of the Hamming parity-check matrix. -/
noncomputable def steaneGenZ (i : Fin 3) : Evolution (bitReg (Fin 7)) :=
  phaseString (hammingParityCheck i)

/-- **The six generators of Figure 10.6**, as a single family `Fin 6 → Evolution`: the three X-type
generators `steaneGenX` followed by the three Z-type generators `steaneGenZ`. -/
noncomputable def steaneStabilizer : Fin 6 → Evolution (bitReg (Fin 7)) :=
  Fin.append steaneGenX steaneGenZ

/-- **Nielsen & Chuang, Exercise 10.32 (logical zero).** Every one of the six Figure-10.6 generators
stabilizes the Steane logical zero `|0_L⟩`. -/
theorem steaneStabilizer_hasEigenstate_one_logicalZero (i : Fin 6) :
    (steaneStabilizer i).HasEigenstate 1 steaneLogicalZero := sorry

/-- **Nielsen & Chuang, Exercise 10.32 (logical one).** Every one of the six Figure-10.6 generators
stabilizes the Steane logical one `|1_L⟩`. -/
theorem steaneStabilizer_hasEigenstate_one_logicalOne (i : Fin 6) :
    (steaneStabilizer i).HasEigenstate 1 steaneLogicalOne := sorry

end AxQM
