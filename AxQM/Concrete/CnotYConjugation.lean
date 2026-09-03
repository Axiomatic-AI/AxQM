/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SqrtSwapCNOT
import AxQM.Concrete.PauliKronecker

/-!
# Concrete: the CNOT conjugation `U Y₁ U† = Y₁ X₂` (Nielsen & Chuang, Exercise 10.37)

How the two-qubit controlled-NOT gate `U` conjugates the Pauli operator `Y₁ = Y ⊗ I` (Pauli `Y` on
the control qubit), as `4 × 4` complex matrices. This is Nielsen & Chuang, *Quantum Computation and
Quantum Information*, **Exercise 10.37** (p. 460).

## Contents

* `twoQubitCNOT_conj_pauliY_kron_pauliI` — the exercise proper:
  `U Y₁ U† = Y ⊗ X`.
* `twoQubitCNOT_conj_pauliY_kron_pauliI_eq_mul` — the same result in Nielsen & Chuang's product
  form `U Y₁ U† = Y₁ X₂`.
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

/-- **Nielsen & Chuang, Exercise 10.37:** the CNOT gate `U` (control = first qubit) conjugates `Y₁ =
Y ⊗ I` to `Y ⊗ X`: `U Y₁ U† = Y ⊗ X`. -/
theorem twoQubitCNOT_conj_pauliY_kron_pauliI :
    twoQubitCNOT * (pauliY ⊗ₖ pauliI) * twoQubitCNOTᴴ = pauliY ⊗ₖ pauliX := sorry

/-- **Nielsen & Chuang, Exercise 10.37, product form:** `U Y₁ U† = Y₁ X₂`, i.e.
`U (Y ⊗ I) U† = (Y ⊗ I)(I ⊗ X)`. -/
theorem twoQubitCNOT_conj_pauliY_kron_pauliI_eq_mul :
    twoQubitCNOT * (pauliY ⊗ₖ pauliI) * twoQubitCNOTᴴ
      = (pauliY ⊗ₖ pauliI) * (pauliI ⊗ₖ pauliX) := sorry

end AxQM.Concrete
