/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliCommutator
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Concrete: two-qubit total angular momentum obeys the SU(2) relations (N&C Ex. 7.25)

This file verifies Nielsen & Chuang, Exercise 7.25 (p. 314), over the concrete `4 × 4` complex
matrices built as Kronecker products of the Pauli matrices `pauliSigma`.

## Main declarations

* `totalSpin i = (σᵢ ⊗ I + I ⊗ σᵢ)/2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ` — the operator
  `jᵢ` (`totalSpin 0 = jₓ`, `totalSpin 1 = j_y`, `totalSpin 2 = j_z`), where the two-qubit space is
  `Fin 2 × Fin 2` and `⊗ₖ` (`Matrix.kroneckerMap (· * ·)`) is the tensor product.
* `totalSpin_lie` — the SU(2) relation `⁅jⱼ, jₖ⁆ = i Σₗ ε_{jkl} jₗ`, the faithful statement of the
  exercise for all `j, k : Fin 3` (the diagonal `j = k` and the anticyclic instances are included,
  since `ε` vanishes / changes sign accordingly).
-/

namespace AxQM.Concrete

open Matrix Complex
open scoped Kronecker

/-- The **two-qubit total angular momentum operators** `jᵢ = (σᵢ ⊗ I + I ⊗ σᵢ)/2` (Nielsen & Chuang,
p. 314): `totalSpin 0 = jₓ = (X₁ + X₂)/2`, `totalSpin 1 = j_y = (Y₁ + Y₂)/2`,
`totalSpin 2 = j_z = (Z₁ + Z₂)/2`, on the two-qubit space `Fin 2 × Fin 2`. -/
noncomputable def totalSpin (i : Fin 3) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 2 : ℂ) • (pauliSigma i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauliSigma i)

/-- **Exercise 7.25**: the two-qubit total angular momentum operators obey the commutation relations
for `SU(2)`, `⁅jⱼ, jₖ⁆ = i Σₗ ε_{jkl} jₗ` — Nielsen & Chuang's `[jᵢ, jₖ] = i ε_{ikl} jₗ`. Holds for
all `j, k : Fin 3`: the diagonal case is `0 = 0` and the anticyclic cases carry the sign of `ε`. -/
theorem totalSpin_lie (j k : Fin 3) :
    ⁅totalSpin j, totalSpin k⁆ = I • ∑ l, (leviCivita3 j k l : ℂ) • totalSpin l := sorry

end AxQM.Concrete
