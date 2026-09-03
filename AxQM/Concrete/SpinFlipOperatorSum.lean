/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.Real.Sqrt
import AxQM.Concrete.PauliKronecker

/-!
# Concrete: the spin-flip channel and its operator-sum representation (N&C, Exercise 8.5)

It computes the operator-sum (Kraus) representation of the single-qubit quantum operation obtained
from the two-qubit "spin-flip" interaction of Nielsen & Chuang, Exercise 8.5 (p. 361).

## The exercise

## Contents

* `matrixPartialTraceRight` — the partial trace over the second (environment) tensor factor of a
  `(a × b)`-indexed matrix, `(tr_env M) i j = Σₑ M (i,e) (j,e)`, packaged as a `ℂ`-linear map.
* `spinFlipScale` — the scalar `1/√2`.
* `spinFlipU` — the interaction unitary `U = (X/√2) ⊗ I + (Y/√2) ⊗ X`.
* `spinFlipKraus` — the operation elements `E₀ = X/√2`, `E₁ = Y/√2`.
* `spinFlipChannel` — the quantum operation `E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)`, with
  `spinFlipChannel_eq_kraus`, the operator-sum representation `E(ρ) = Σₖ Eₖ ρ Eₖ†`.
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

/-- The **partial trace over the second (environment) tensor factor** of a matrix indexed by a
product type `a × b`: `(tr_env M) i j = Σₑ M (i, e) (j, e)`, i.e. `Σₑ (I ⊗ ⟨e|) M (I ⊗ |e⟩)` read
entrywise. Packaged as a `ℂ`-linear map so that `map_add`, `map_smul`, `map_sum` are available. -/
def matrixPartialTraceRight {a b : Type*} [Fintype b] :
    Matrix (a × b) (a × b) ℂ →ₗ[ℂ] Matrix a a ℂ where
  toFun M := Matrix.of fun i j => ∑ e, M (i, e) (j, e)
  map_add' M N := by ext i j; simp [Finset.sum_add_distrib]
  map_smul' c M := by ext i j; simp [Finset.mul_sum]

/-- The scalar `1/√2 = (√2)⁻¹` (as a complex number), the amplitude appearing in the spin-flip
interaction `U = (X/√2) ⊗ I + (Y/√2) ⊗ X`. -/
noncomputable def spinFlipScale : ℂ := (Real.sqrt 2)⁻¹

/-- The **spin-flip interaction unitary** (Nielsen & Chuang, eq. 8.17):
`U = (X/√2) ⊗ I + (Y/√2) ⊗ X`, where the first Kronecker factor acts on the system and the second
on the environment. Both `X ⊗ I` and `Y ⊗ X` are Hermitian, so `U` is Hermitian; the Pauli
anticommutation `{X, Y} = 0` makes it an involution, hence unitary. -/
noncomputable def spinFlipU : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  spinFlipScale • (pauliX ⊗ₖ pauliI) + spinFlipScale • (pauliY ⊗ₖ pauliX)

/-- The **operation elements** (Kraus operators) of the spin-flip channel: `E₀ = X/√2` and `E₁ =
Y/√2` (Nielsen & Chuang, eq. 8.17). -/
noncomputable def spinFlipKraus : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![spinFlipScale • pauliX, spinFlipScale • pauliY]

/-- The **spin-flip quantum operation** `E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)`. -/
noncomputable def spinFlipChannel (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  matrixPartialTraceRight (spinFlipU * (ρ ⊗ₖ ketBra 0 0) * spinFlipUᴴ)

/-- **The operator-sum (Kraus) representation of the spin-flip channel** (Nielsen & Chuang, eqs.
8.9–8.10 for Exercise 8.5). This is the answer the exercise asks for: the spin-flip interaction
produces the operator-sum quantum operation with these two operation elements. -/
theorem spinFlipChannel_eq_kraus (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinFlipChannel ρ = ∑ k, spinFlipKraus k * ρ * (spinFlipKraus k)ᴴ := sorry

end AxQM.Concrete
