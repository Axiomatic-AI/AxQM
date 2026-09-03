/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliKronecker
import AxQM.Concrete.Sqrt2IntegerMatrix

/-!
# Concrete: explicit CNOT conjugation of the two-qubit Pauli generators (N&C Ex. 10.36)

How the two-qubit controlled-NOT gate `U = CNOT` (control = qubit 1, target = qubit 2) conjugates
the four Pauli generators of the two-qubit Pauli group — Nielsen & Chuang, Exercise 10.36 (p. 460).

## Contents

* `pauliX1`, `pauliX2`, `pauliZ1`, `pauliZ2` — the two-qubit generators `X ⊗ I`, `I ⊗ X`, `Z ⊗ I`,
  `I ⊗ Z` as `4 × 4` matrices, defined via `flattenFin4`.
* `cnotMatrix_conj_pauliX1`, `cnotMatrix_conj_pauliX2`, `cnotMatrix_conj_pauliZ1`,
  `cnotMatrix_conj_pauliZ2` — **Exercise 10.36**: the four conjugation identities
  `U X₁ U† = X₁X₂`, `U X₂ U† = X₂`, `U Z₁ U† = Z₁`, `U Z₂ U† = Z₁Z₂`, where the right-hand
  products `X₁X₂` and `Z₁Z₂` are the literal matrix products `pauliX1 * pauliX2` and
  `pauliZ1 * pauliZ2` (`pauliX2`, `pauliZ1` on the two "trivial" cases).
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

/-- The two-qubit generator `X₁ = X ⊗ I` (Pauli `X` on the control qubit), as the `4 × 4` matrix
`flattenFin4 (X ⊗ₖ I)` in big-endian computational-basis order. -/
noncomputable def pauliX1 : Matrix (Fin 4) (Fin 4) ℂ := flattenFin4 (pauliX ⊗ₖ pauliI)

/-- The two-qubit generator `X₂ = I ⊗ X` (Pauli `X` on the target qubit), as the `4 × 4` matrix
`flattenFin4 (I ⊗ₖ X)` in big-endian computational-basis order. -/
noncomputable def pauliX2 : Matrix (Fin 4) (Fin 4) ℂ := flattenFin4 (pauliI ⊗ₖ pauliX)

/-- The two-qubit generator `Z₁ = Z ⊗ I` (Pauli `Z` on the control qubit), as the `4 × 4` matrix
`flattenFin4 (Z ⊗ₖ I)` in big-endian computational-basis order. -/
noncomputable def pauliZ1 : Matrix (Fin 4) (Fin 4) ℂ := flattenFin4 (pauliZ ⊗ₖ pauliI)

/-- The two-qubit generator `Z₂ = I ⊗ Z` (Pauli `Z` on the target qubit), as the `4 × 4` matrix
`flattenFin4 (I ⊗ₖ Z)` in big-endian computational-basis order. -/
noncomputable def pauliZ2 : Matrix (Fin 4) (Fin 4) ℂ := flattenFin4 (pauliI ⊗ₖ pauliZ)

/-- **Exercise 10.36** (first relation): CNOT conjugates `X` on the control into `X` on both wires,
`U X₁ U† = X₁X₂`. -/
theorem cnotMatrix_conj_pauliX1 :
    cnotMatrix * pauliX1 * cnotMatrixᴴ = pauliX1 * pauliX2 := sorry

/-- **Exercise 10.36** (second relation): CNOT leaves target `X` unchanged: `U X₂ U† = X₂`. -/
theorem cnotMatrix_conj_pauliX2 :
    cnotMatrix * pauliX2 * cnotMatrixᴴ = pauliX2 := sorry

/-- **Exercise 10.36** (third relation): CNOT leaves control `Z` unchanged: `U Z₁ U† = Z₁`. -/
theorem cnotMatrix_conj_pauliZ1 :
    cnotMatrix * pauliZ1 * cnotMatrixᴴ = pauliZ1 := sorry

/-- **Exercise 10.36** (fourth relation): CNOT conjugates `Z` on the target into `Z` on both wires,
`U Z₂ U† = Z₁Z₂`. -/
theorem cnotMatrix_conj_pauliZ2 :
    cnotMatrix * pauliZ2 * cnotMatrixᴴ = pauliZ1 * pauliZ2 := sorry

end AxQM.Concrete
