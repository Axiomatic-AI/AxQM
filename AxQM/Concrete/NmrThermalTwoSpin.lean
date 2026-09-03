/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliKronecker
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Concrete: the two-spin NMR thermal-equilibrium data (Nielsen & Chuang, Exercise 7.36, `n = 2`)

The matrix data for the two-spin case of Nielsen & Chuang, Exercise 7.36 (eq. 7.142).
-/

namespace AxQM.Concrete

open Matrix Complex
open scoped Kronecker

/-- The **four Zeeman energy levels** of the two-spin NMR Hamiltonian `H = ℏ(ω_A Z₁ + ω_B Z₂)`, as
a real vector: `ℏ·(ω_A+ω_B, ω_A−ω_B, −ω_A+ω_B, −ω_A−ω_B)` (the diagonal of `H` in the
computational basis `|00⟩, |01⟩, |10⟩, |11⟩`, as `Z₁ = diag(1,1,−1,−1)`, `Z₂ = diag(1,−1,1,−1)`). -/
noncomputable def nmrZeemanTwoSpinDiag (ℏ ωA ωB : ℝ) : Fin 4 → ℝ :=
  ![ℏ * (ωA + ωB), ℏ * (ωA - ωB), ℏ * (-ωA + ωB), ℏ * (-ωA - ωB)]

/-- The **two-spin NMR (Zeeman) Hamiltonian** `H = ℏ(ω_A Z₁ + ω_B Z₂) = ℏ(ω_A Z⊗I + ω_B I⊗Z)` of
Nielsen & Chuang §7.7.1, as a `4 × 4` complex matrix in the computational basis
`|00⟩, |01⟩, |10⟩, |11⟩` (flattened from the two-factor tensor via `flattenFin4`). Here `ω_A, ω_B`
are the two precession (Larmor) frequencies and `ℏ` is Planck's constant. -/
noncomputable def nmrZeemanTwoSpinMatrix (ℏ ωA ωB : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (ℏ : ℂ) • flattenFin4 ((ωA : ℂ) • pauliZ ⊗ₖ pauliI + (ωB : ℂ) • pauliI ⊗ₖ pauliZ)

/-- The two-spin Zeeman Hamiltonian is **diagonal** in the computational basis, with the four Zeeman
levels on the diagonal: `nmrZeemanTwoSpinMatrix ℏ ω_A ω_B = diag(ℏ(ω_A+ω_B), ℏ(ω_A−ω_B),
ℏ(−ω_A+ω_B), ℏ(−ω_A−ω_B))`. -/
theorem nmrZeemanTwoSpinMatrix_eq_diagonal (ℏ ωA ωB : ℝ) :
    nmrZeemanTwoSpinMatrix ℏ ωA ωB
      = diagonal (fun i => ((nmrZeemanTwoSpinDiag ℏ ωA ωB i : ℝ) : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nmrZeemanTwoSpinMatrix, nmrZeemanTwoSpinDiag, flattenFin4, pauliZ, pauliI,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.add_apply, Matrix.smul_apply,
      sub_eq_add_neg]

/-- The two-spin Zeeman Hamiltonian matrix is **Hermitian** (it is diagonal with real entries). -/
theorem nmrZeemanTwoSpinMatrix_isHermitian (ℏ ωA ωB : ℝ) :
    (nmrZeemanTwoSpinMatrix ℏ ωA ωB).IsHermitian := by
  rw [nmrZeemanTwoSpinMatrix_eq_diagonal]
  exact isHermitian_diagonal_of_self_adjoint _ (by funext i; exact Complex.conj_ofReal _)

/-- The **diagonal populations of the two-spin high-temperature thermal state** `2⁻²(I − βH)` in the
resonance case `ω_A = 4ω_B` of Nielsen & Chuang eq. 7.142: `¼·(1 − 5βℏω_B, 1 − 3βℏω_B, 1 + 3βℏω_B,
1 + 5βℏω_B)`. Here `β = 1/(k_B T)`. -/
noncomputable def nmrThermalPopTwoSpin (β ℏ ωB : ℝ) : Fin 4 → ℝ :=
  ![(4 : ℝ)⁻¹ * (1 - 5 * (β * ℏ * ωB)), (4 : ℝ)⁻¹ * (1 - 3 * (β * ℏ * ωB)),
    (4 : ℝ)⁻¹ * (1 + 3 * (β * ℏ * ωB)), (4 : ℝ)⁻¹ * (1 + 5 * (β * ℏ * ωB))]

/-- The eq. 7.142 thermal populations are **nonnegative** whenever `(5βℏω_B)² ≤ 1` — the two-spin
high-temperature / positivity condition (all four Bloch-diagonal entries lie in `[0,1]`). -/
theorem nmrThermalPopTwoSpin_nonneg (β ℏ ωB : ℝ) (h : (5 * (β * ℏ * ωB)) ^ 2 ≤ 1) (i : Fin 4) :
    0 ≤ nmrThermalPopTwoSpin β ℏ ωB i := by
  fin_cases i <;> simp [nmrThermalPopTwoSpin] <;>
    nlinarith [h, sq_nonneg (5 * (β * ℏ * ωB) - 1), sq_nonneg (5 * (β * ℏ * ωB) + 1)]

/-- The eq. 7.142 thermal populations **sum to one** (the trace of the density matrix). Stated over
`ℂ` for the trace computation. -/
theorem nmrThermalPopTwoSpin_sum (β ℏ ωB : ℝ) :
    ∑ i, ((nmrThermalPopTwoSpin β ℏ ωB i : ℝ) : ℂ) = 1 := by
  simp [nmrThermalPopTwoSpin, Fin.sum_univ_four]; ring

/-- **The `n = 2` high-temperature thermal matrix is the eq. 7.142 diagonal populations matrix**
(resonance case `ω_A = 4ω_B`): `2⁻²(I − βH) = ¼(I − β·nmrZeemanTwoSpinMatrix) = diag
nmrThermalPopTwoSpin`. The `¼` prefactor is written `((4 : ℕ) : ℂ)⁻¹` to match `1/dim (qudit 4)`. -/
theorem nmrHighTempTwoSpinMatrix_eq (β ℏ ωB : ℝ) :
    ((4 : ℕ) : ℂ)⁻¹ •
        ((1 : Matrix (Fin 4) (Fin 4) ℂ) - (β : ℂ) • nmrZeemanTwoSpinMatrix ℏ (4 * ωB) ωB)
      = diagonal (fun i => ((nmrThermalPopTwoSpin β ℏ ωB i : ℝ) : ℂ)) := by
  rw [nmrZeemanTwoSpinMatrix_eq_diagonal]
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
      smul_eq_mul, nmrZeemanTwoSpinDiag, nmrThermalPopTwoSpin]
    fin_cases i <;> push_cast <;> ring
  · simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_ne hij,
      Matrix.diagonal_apply_ne _ hij, smul_zero, sub_zero]

end AxQM.Concrete
