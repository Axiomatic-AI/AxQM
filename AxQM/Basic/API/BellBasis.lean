/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BellState
import AxQM.Basic.Composite

/-!
# AxQM.Basic.API — the Bell basis of the two-qubit system

The four **Bell states** `|β_xy⟩` (Nielsen & Chuang, §1.3.6 / §2.3, eqs. (2.134)–(2.137))
as pure states of the two-qubit system `qubit ⊗ qubit`, and the proof that they form an
**orthonormal basis** of its state space (Nielsen & Chuang, Exercise 2.69).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- Inner product of two **computational two-qubit** vectors `|ab⟩` and `|cd⟩`. -/
theorem qubitBasis_tmul_inner (a b c d : Fin 2) :
    inner ℂ ((qubitBasis a ⊗ qubitBasis b).vec) ((qubitBasis c ⊗ qubitBasis d).vec)
      = (if a = c then (1 : ℂ) else 0) * (if b = d then 1 else 0) := by
  rw [PureState.tmul_vec, PureState.tmul_vec]
  change inner ℂ ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
      ((qubitBasis c).vec ⊗ₜ[ℂ] (qubitBasis d).vec) = _
  rw [TensorProduct.inner_tmul ℂ, qubitBasis_inner_qubitBasis, qubitBasis_inner_qubitBasis]

/-- The underlying two-qubit vector of the Bell state `|β_xy⟩ = (|0,y⟩ + (-1)ˣ |1, ȳ⟩)/√2`,
where `ȳ = y + 1` is the bit-flip of `y`. -/
def bellBasisVec (x y : Fin 2) : (qubit ⊗ qubit).space :=
  (Real.sqrt 2 : ℂ)⁻¹ •
    ((qubitBasis 0 ⊗ qubitBasis y).vec
      + (-1 : ℂ) ^ (x : ℕ) • (qubitBasis 1 ⊗ qubitBasis (y + 1)).vec)

/-- The squared magnitude of the Bell normalisation `(√2)⁻¹`: `conj((√2)⁻¹) · (√2)⁻¹ = ½`. -/
theorem conj_sqrtTwoInv_mul_self :
    (starRingEnd ℂ) ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
  rw [map_inv₀, Complex.conj_ofReal, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- **Inner-product table of the Bell vectors:** `⟨β_xy|β_x'y'⟩ = δ_{(x,y),(x',y')}` — both the
normalization (the diagonal) and the mutual orthogonality (the off-diagonal) of Exercise 2.69. -/
theorem bellBasisVec_inner (x y x' y' : Fin 2) :
    inner ℂ (bellBasisVec x y) (bellBasisVec x' y') = if (x, y) = (x', y') then 1 else 0 := by
  simp only [bellBasisVec]
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, conj_sqrtTwoInv_mul_self]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    qubitBasis_tmul_inner, map_pow, map_neg, map_one]
  fin_cases x <;> fin_cases x' <;> fin_cases y <;> fin_cases y' <;>
    norm_num [Prod.ext_iff]

/-- Each Bell vector is a **unit vector**: `⟨β_xy|β_xy⟩ = 1`. -/
theorem bellBasisVec_norm (x y : Fin 2) : ‖bellBasisVec x y‖ = 1 := by
  rw [← Real.sqrt_one, norm_eq_sqrt_re_inner (𝕜 := ℂ), bellBasisVec_inner]; simp

/-- The **Bell state** `|β_xy⟩ = (|0,y⟩ + (-1)ˣ |1, ȳ⟩)/√2` as a pure state of the two-qubit
system `qubit ⊗ qubit`, in Nielsen & Chuang's `β_xy` indexing.  The four states are
`|β₀₀⟩ = (|00⟩+|11⟩)/√2`, `|β₀₁⟩ = (|01⟩+|10⟩)/√2`, `|β₁₀⟩ = (|00⟩−|11⟩)/√2` and
`|β₁₁⟩ = (|01⟩−|10⟩)/√2`. -/
def bellState (x y : Fin 2) : PureState (qubit ⊗ qubit) where
  vec := bellBasisVec x y
  normalized := bellBasisVec_norm x y

@[simp]
theorem bellState_vec (x y : Fin 2) : (bellState x y).vec = bellBasisVec x y := rfl

/-- **The Bell states are orthonormal** (Nielsen & Chuang, Exercise 2.69, first half): the family
`(x, y) ↦ |β_xy⟩` is an orthonormal family of pure states. -/
theorem bellState_orthonormal :
    Orthonormal ℂ (fun p : Fin 2 × Fin 2 => (bellState p.1 p.2).vec) := by
  rw [orthonormal_iff_ite]
  rintro ⟨x, y⟩ ⟨x', y'⟩
  simpa only [bellState_vec] using bellBasisVec_inner x y x' y'

/-- The two-qubit state space has **dimension `4 = 2·2`**, equal to the number of Bell states. -/
theorem bell_card_eq :
    Fintype.card (Fin 2 × Fin 2) = Module.finrank ℂ (qubit ⊗ qubit).space := by
  change Fintype.card (Fin 2 × Fin 2)
    = Module.finrank ℂ (TensorProduct ℂ (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2)))
  rw [Module.finrank_tensorProduct, finrank_euclideanSpace_fin]
  decide

/-- **Exercise 2.69:** the four **Bell states form an orthonormal basis** of the two-qubit state
space.  Packaged as an `OrthonormalBasis (Fin 2 × Fin 2) ℂ` of `(qubit ⊗ qubit).space`. -/
def bellBasis : OrthonormalBasis (Fin 2 × Fin 2) ℂ (qubit ⊗ qubit).space :=
  (basisOfOrthonormalOfCardEqFinrank bellState_orthonormal bell_card_eq).toOrthonormalBasis
    (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact bellState_orthonormal)

@[simp]
theorem bellBasis_apply (p : Fin 2 × Fin 2) : bellBasis p = (bellState p.1 p.2).vec := sorry

end AxQM
