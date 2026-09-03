/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliString
import AxQM.Concrete.HadamardPauliConjugation
import AxQM.Concrete.AxisAngleGateValues
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Concrete: local single-qubit basis change reducing `X ⊗ Y ⊗ Z` to `Z ⊗ Z ⊗ Z`

## Main results
* `kronFamily` — the `n`-fold tensor product `⨂ₖ Aₖ` of a family of single-qubit operators,
  defined entrywise `(⨂ₖ Aₖ)(i,j) = ∏ₖ Aₖ(iₖ)(jₖ)` on the register index `Fin n → Fin 2`.
* `kronFamily_mul` — the **mixed-product property** `(⨂ₖ Aₖ)(⨂ₖ Bₖ) = ⨂ₖ (Aₖ Bₖ)`, with
  `kronFamily_conjTranspose` (`(⨂ₖ Aₖ)ᴴ = ⨂ₖ Aₖᴴ`), `kronFamily_one` (`⨂ₖ 1 = 1`) and
  `kronFamily_smul_family` (`⨂ₖ (cₖ • Aₖ) = (∏ₖ cₖ) • ⨂ₖ Aₖ`).
* `basisChangeY` / `sMatrix_conj_pauliX` / `sMatrix_conj_pauliZ` — the `Y` basis-change gate `S·H`
  and the single-qubit phase-gate tableau `S·X·Sᴴ = Y`, `S·Z·Sᴴ = Z` (N&C Ex 10.39).
* `basisChangeFamily` / `kronFamilyStd` — the local family `B = (H, SH, I)` and its flat-register
  tensor product, with their unitarity.
-/

open Matrix Complex

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- The **`n`-fold tensor product** `A₀ ⊗ A₁ ⊗ ⋯ ⊗ A_{n-1}` of a family of single-qubit operators `A
: Fin n → M₂(ℂ)`, as an operator on the `n`-qubit register `Fin n → Fin 2`, defined entrywise by
the product of the per-qubit entries `(⨂ₖ Aₖ)(i,j) = ∏ₖ Aₖ(iₖ)(jₖ)`. -/
def kronFamily (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun i j => ∏ k, A k (i k) (j k)

@[simp]
theorem kronFamily_apply (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin n → Fin 2) :
    kronFamily A i j = ∏ k, A k (i k) (j k) := rfl

/-- A Pauli string is the tensor product of its per-qubit Pauli factors:
`pauliString g = kronFamily (fun k => pauli (g k))`. -/
theorem pauliString_eq_kronFamily (g : Fin n → Fin 4) :
    pauliString g = kronFamily (fun k => pauli (g k)) := rfl

/-- **Mixed-product property of the tensor product** `(⨂ₖ Aₖ)(⨂ₖ Bₖ) = ⨂ₖ (Aₖ Bₖ)`. -/
theorem kronFamily_mul (A B : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    kronFamily A * kronFamily B = kronFamily (fun k => A k * B k) := by
  ext i j
  simp only [kronFamily, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun l _ => Finset.prod_mul_distrib.symm

/-- The conjugate transpose of a tensor product is the tensor product of the conjugate transposes,
`(⨂ₖ Aₖ)ᴴ = ⨂ₖ Aₖᴴ`. -/
theorem kronFamily_conjTranspose (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (kronFamily A)ᴴ = kronFamily (fun k => (A k)ᴴ) := by
  ext i j
  rw [Matrix.conjTranspose_apply, kronFamily_apply, kronFamily_apply, ← starRingEnd_apply,
    map_prod]
  exact Finset.prod_congr rfl fun k _ => by rw [starRingEnd_apply, Matrix.conjTranspose_apply]

/-- The tensor product of identities is the identity, `⨂ₖ 1 = 1`. -/
theorem kronFamily_one : kronFamily (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext i j
  simp only [kronFamily_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- Pulling per-qubit scalars out of a tensor product: `⨂ₖ (cₖ • Aₖ) = (∏ₖ cₖ) • ⨂ₖ Aₖ`. -/
theorem kronFamily_smul_family (c : Fin n → ℂ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    kronFamily (fun k => c k • A k) = (∏ k, c k) • kronFamily A := by
  ext i j
  simp only [kronFamily_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib]

/-- The **`Y` basis-change gate** `S·H` (phase gate after Hadamard). -/
noncomputable def basisChangeY : Matrix (Fin 2) (Fin 2) ℂ := sMatrix * hadamardC

/-- **Phase-gate conjugation** `S·X·Sᴴ = Y` (N&C Exercise 10.39): the phase gate `S = diag(1, i)`
rotates `X` into `Y`. -/
theorem sMatrix_conj_pauliX : sMatrix * pauliX * sMatrixᴴ = pauliY := sorry

/-- **Phase-gate conjugation** `S·Z·Sᴴ = Z` (N&C Exercise 10.39): the phase gate `S = diag(1, i)`
fixes `Z`. -/
theorem sMatrix_conj_pauliZ : sMatrix * pauliZ * sMatrixᴴ = pauliZ := sorry

/-- The `Y` basis-change gate is unitary: `(SH)(SH)ᴴ = 1`. -/
theorem basisChangeY_mul_conjTranspose : basisChangeY * basisChangeYᴴ = 1 := by
  have hHadj : hadamardCᴴ = hadamardC := hadamardC_isHermitian
  have hS : sMatrix * sMatrixᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp sMatrix_mem_unitaryGroup
  rw [basisChangeY, Matrix.conjTranspose_mul, hHadj]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc hadamardC, hadamardC_mul_self, Matrix.one_mul, hS]

/-- The `Y` basis-change gate is unitary: `(SH)ᴴ(SH) = 1`. -/
theorem basisChangeY_conjTranspose_mul : basisChangeYᴴ * basisChangeY = 1 := by
  have hHadj : hadamardCᴴ = hadamardC := hadamardC_isHermitian
  have hS : sMatrixᴴ * sMatrix = 1 := Matrix.mem_unitaryGroup_iff'.mp sMatrix_mem_unitaryGroup
  rw [basisChangeY, Matrix.conjTranspose_mul, hHadj]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc sMatrixᴴ, hS, Matrix.one_mul, hadamardC_mul_self]

/-- The **local basis-change family** `B = (B₁, B₂, B₃) = (H, SH, I)` for Exercise 4.51: the three
single-qubit gates whose tensor product `kronFamily basisChangeFamily` conjugates `Z ⊗ Z ⊗ Z` to
`X ⊗ Y ⊗ Z`. -/
noncomputable def basisChangeFamily : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![hadamardC, basisChangeY, 1]

/-- Each local gate `Bₖ` is unitary: `Bₖ · Bₖᴴ = 1`. -/
theorem basisChangeFamily_mul_conjTranspose (k : Fin 3) :
    basisChangeFamily k * (basisChangeFamily k)ᴴ = 1 := by
  fin_cases k
  · simpa [basisChangeFamily] using
      (by rw [hadamardC_isHermitian]; exact hadamardC_mul_self :
        hadamardC * hadamardCᴴ = 1)
  · simpa [basisChangeFamily] using basisChangeY_mul_conjTranspose
  · simp [basisChangeFamily]

/-- The tensor unitary `B = H ⊗ SH ⊗ I` is unitary: `B · Bᴴ = 1`. -/
theorem kronFamily_basisChangeFamily_mul_conjTranspose :
    kronFamily basisChangeFamily * (kronFamily basisChangeFamily)ᴴ = 1 := by
  rw [kronFamily_conjTranspose, kronFamily_mul]
  simp only [basisChangeFamily_mul_conjTranspose, kronFamily_one]

/-- The **Std-indexed tensor product** `⨂ₖ Aₖ` on the flat register `Fin (2ⁿ)`: `kronFamily A`
reindexed from bit strings `Fin n → Fin 2` to `Fin (2ⁿ)` along `finFunctionFinEquiv`. This is the
operator `B = ⨂ₖ Aₖ` in the flat computational-basis ordering that the `n`-qubit register
`qudit (2ⁿ)` uses. -/
noncomputable def kronFamilyStd (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (kronFamily A).submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm

/-- The Std basis change is unitary: `B · Bᴴ = 1` on `Fin (2³)`. -/
theorem kronFamilyStd_basisChangeFamily_mul_conjTranspose :
    kronFamilyStd basisChangeFamily * (kronFamilyStd basisChangeFamily)ᴴ = 1 := by
  simp only [kronFamilyStd, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, kronFamily_basisChangeFamily_mul_conjTranspose,
    Matrix.submatrix_one_equiv]

end AxQM.Concrete
