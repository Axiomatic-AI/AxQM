/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Complex.Basic

/-!
# The Hilbert–Schmidt inner product on matrices

For a finite index type `n` and an `RCLike` field `𝕜`, the space `Matrix n n 𝕜` of operators on
`𝕜ⁿ` carries the **Hilbert–Schmidt** (or **trace**) inner product
`(A, B) = tr(Aᴴ * B)`. This file records that `(·, ·)` is genuinely an inner product, computes
the dimension of the operator space, and exhibits an orthonormal basis of Hermitian matrices —
**Nielsen & Chuang, Exercise 2.39** (*Quantum Computation and Quantum Information*, §2.1.8,
eq. (2.65)), parts (1), (2) and (3).

## Main definitions and results

* `Matrix.hsInner`: the Hilbert–Schmidt inner product `(A, B) = tr(Aᴴ * B)` as a bare function.
* `Matrix.hsInnerCore`: the proof that `Matrix.hsInner` is an inner product, packaged as an
  `InnerProductSpace.Core` — this is part (1) of the exercise. Its fields are exactly the inner
  product axioms: conjugate symmetry, positive semidefiniteness, definiteness, additivity, and
  conjugate linearity in the first argument.
* `Matrix.finrank_eq_card_sq`: `Module.finrank 𝕜 (Matrix n n 𝕜) = (Fintype.card n) ^ 2` — part (2)
  of the exercise (`dim L_V = d²` for `dim V = d`).
* `Matrix.gellMann` (over `ℂ`, with `n` linearly ordered): the generalised Gell–Mann family of `d²`
  Hermitian matrices, shown to be Hermitian and orthonormal under
  `Matrix.hsInner` (`Matrix.gellMann_orthonormal`); `Matrix.hermitianOrthonormalBasis` bundles them
  into a `Module.Basis (n × n) ℂ (Matrix n n ℂ)` — this is part (3).
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- The **Hilbert–Schmidt** (or **trace**) inner product on operators, `(A, B) = tr(Aᴴ * B)`
(Nielsen & Chuang eq. (2.65)). -/
def hsInner (A B : Matrix n n 𝕜) : 𝕜 := (Aᴴ * B).trace

theorem hsInner_apply (A B : Matrix n n 𝕜) : hsInner A B = (Aᴴ * B).trace := rfl

section Bilinear

/-- Additivity of `hsInner` in the first argument. -/
theorem hsInner_add_left (A B C : Matrix n n 𝕜) :
    hsInner (A + B) C = hsInner A C + hsInner B C := by
  simp only [hsInner_apply, conjTranspose_add, add_mul, trace_add]

/-- Subtractivity of `hsInner` in the first argument. -/
theorem hsInner_sub_left (A B C : Matrix n n 𝕜) :
    hsInner (A - B) C = hsInner A C - hsInner B C := by
  simp only [hsInner_apply, conjTranspose_sub, sub_mul, trace_sub]

/-- `hsInner` is conjugate-linear in the first argument. -/
theorem hsInner_smul_left (r : 𝕜) (A B : Matrix n n 𝕜) :
    hsInner (r • A) B = starRingEnd 𝕜 r * hsInner A B := by
  simp only [hsInner_apply, conjTranspose_smul, smul_mul_assoc, trace_smul, smul_eq_mul,
    starRingEnd_apply]

/-- `hsInner` is linear in the second argument (scalar multiplication). -/
theorem hsInner_smul_right (r : 𝕜) (A B : Matrix n n 𝕜) :
    hsInner A (r • B) = r * hsInner A B := by
  simp only [hsInner_apply, mul_smul, trace_smul, smul_eq_mul]

@[simp]
theorem hsInner_zero_right (A : Matrix n n 𝕜) : hsInner A 0 = 0 := by
  simp only [hsInner_apply, mul_zero, trace_zero]

/-- `hsInner` distributes over a finite sum in the second argument. -/
theorem hsInner_sum_right {ι : Type*} (A : Matrix n n 𝕜) (s : Finset ι)
    (f : ι → Matrix n n 𝕜) : hsInner A (∑ i ∈ s, f i) = ∑ i ∈ s, hsInner A (f i) := by
  simp only [hsInner_apply, Matrix.mul_sum, Matrix.trace_sum]

end Bilinear

/-- **Nielsen & Chuang, Exercise 2.39 (1).** The Hilbert–Schmidt form `(A, B) = tr(Aᴴ * B)` is an
inner product on `Matrix n n 𝕜`, packaged as an `InnerProductSpace.Core`. Its fields are the
inner product axioms. -/
@[implicit_reducible]
noncomputable def hsInnerCore : InnerProductSpace.Core 𝕜 (Matrix n n 𝕜) where
  inner A B := hsInner A B
  conj_inner_symm A B := by
    simp only [hsInner_apply, starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose]
  re_inner_nonneg A := by
    simp only [hsInner_apply]
    exact (RCLike.nonneg_iff.mp (posSemidef_conjTranspose_mul_self A).trace_nonneg).1
  add_left A B C := hsInner_add_left A B C
  smul_left A B r := hsInner_smul_left r A B
  definite A h := trace_conjTranspose_mul_self_eq_zero_iff.mp h

/-- **Nielsen & Chuang, Exercise 2.39 (2).** If `V` is a Hilbert space of dimension `d`, then the
operator space `L_V` has dimension `d²`. -/
theorem finrank_eq_card_sq :
    Module.finrank 𝕜 (Matrix n n 𝕜) = Fintype.card n ^ 2 := by
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, sq]

section MatrixUnits

variable [DecidableEq n]

/-- The Hilbert–Schmidt inner product against a matrix unit reads off an entry:
`⟪single a b 1, M⟫ = M a b`. -/
theorem hsInner_single_left (a b : n) (M : Matrix n n 𝕜) :
    hsInner (single a b 1) M = M a b := by
  rw [hsInner_apply, conjTranspose_single, star_one, trace_single_mul, one_smul]

end MatrixUnits

section HermitianBasis

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- The normalisation `(√2)⁻¹` is fixed by complex conjugation (it is real). -/
theorem conj_sqrt2inv : starRingEnd ℂ ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [← Complex.ofReal_inv, Complex.conj_ofReal]

/-- `(√2)⁻¹ · (√2)⁻¹ = 2⁻¹`. -/
theorem sqrt2inv_mul_self : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 2⁻¹ := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `((√2)⁻¹)² = 2⁻¹`. -/
theorem sqrt2inv_sq : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 2⁻¹ := by
  rw [sq, sqrt2inv_mul_self]

/-- The **generalised Gell–Mann family**. For `j < k` the symmetric combination `(Eⱼₖ + Eₖⱼ)/√2`,
for `j > k` the antisymmetric `i(Eₖⱼ − Eⱼₖ)/√2`, and on the diagonal the matrix unit `Eⱼⱼ`. They
form an orthonormal (under `Matrix.hsInner`) basis of Hermitian matrices for `L_V` — **Nielsen &
Chuang, Exercise 2.39 (3)**. -/
noncomputable def gellMann (p : n × n) : Matrix n n ℂ :=
  if p.1 < p.2 then (Real.sqrt 2 : ℂ)⁻¹ • (single p.1 p.2 1 + single p.2 p.1 1)
  else if p.2 < p.1 then
    (Real.sqrt 2 : ℂ)⁻¹ • (Complex.I • (single p.2 p.1 1 - single p.1 p.2 1))
  else single p.1 p.1 1

/-- Reading the Hilbert–Schmidt inner product of a Gell–Mann matrix against an arbitrary `M`
in terms of the entries of `M`. -/
theorem hsInner_gellMann_left (p : n × n) (M : Matrix n n ℂ) :
    hsInner (gellMann p) M =
      if p.1 < p.2 then (Real.sqrt 2 : ℂ)⁻¹ * (M p.1 p.2 + M p.2 p.1)
      else if p.2 < p.1 then (Real.sqrt 2 : ℂ)⁻¹ * Complex.I * (M p.1 p.2 - M p.2 p.1)
      else M p.1 p.1 := by
  rw [gellMann]
  split_ifs with h1 h2
  · rw [hsInner_smul_left, hsInner_add_left, hsInner_single_left, hsInner_single_left,
      conj_sqrt2inv]
  · rw [hsInner_smul_left, hsInner_smul_left, hsInner_sub_left, hsInner_single_left,
      hsInner_single_left, conj_sqrt2inv, Complex.conj_I]
    ring
  · rw [hsInner_single_left]

omit [Fintype n] in
/-- Entrywise values of a Gell–Mann matrix, in terms of matrix-unit entries. -/
theorem gellMann_apply (p : n × n) (a b : n) :
    (gellMann p) a b =
      if p.1 < p.2 then
        (Real.sqrt 2 : ℂ)⁻¹ * (single p.1 p.2 (1 : ℂ) a b + single p.2 p.1 1 a b)
      else if p.2 < p.1 then
        (Real.sqrt 2 : ℂ)⁻¹ * Complex.I * (single p.2 p.1 (1 : ℂ) a b - single p.1 p.2 1 a b)
      else single p.1 p.1 (1 : ℂ) a b := by
  rw [gellMann]
  split_ifs with h1 h2 <;>
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, mul_assoc]

set_option maxHeartbeats 400000 in -- `split_ifs` fan-out over the nine order-trichotomy branches
/-- **Nielsen & Chuang, Exercise 2.39 (3), orthonormality.** The generalised Gell–Mann family is
orthonormal under the Hilbert–Schmidt inner product: `⟪gellMann p, gellMann q⟫ = δ_{p,q}`. -/
theorem gellMann_orthonormal (p q : n × n) :
    hsInner (gellMann p) (gellMann q) = if p = q then 1 else 0 := by
  obtain ⟨x, y⟩ := p
  obtain ⟨s, t⟩ := q
  rw [hsInner_gellMann_left]
  simp only [gellMann_apply, single_apply, Prod.ext_iff]
  rcases lt_trichotomy x y with hxy | hxy | hxy <;>
    rcases lt_trichotomy s t with hst | hst | hst <;>
    simp only [hxy, hst, lt_irrefl, if_true, if_false] <;>
    split_ifs <;>
    first
      | rfl
      | (exfalso; casesm* _ ∧ _ <;> subst_vars <;> first | order | tauto)
      | (ring_nf; rw [sqrt2inv_sq]; norm_num)
      | ring

set_option linter.unusedFintypeInType false in
/-- The generalised Gell–Mann family is linearly independent. -/
theorem gellMann_linearIndependent : LinearIndependent ℂ (gellMann (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have hz : hsInner (gellMann q) (∑ p, g p • gellMann p) = 0 := by
    rw [hg]; exact hsInner_zero_right _
  rw [hsInner_sum_right] at hz
  simp only [hsInner_smul_right, gellMann_orthonormal, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at hz
  exact hz

variable [Nonempty n]

/-- **Nielsen & Chuang, Exercise 2.39 (3).** The generalised Gell–Mann family is an (orthonormal,
Hermitian) basis of the operator space `L_V = Matrix n n ℂ`, indexed by `n × n`, hence of
dimension `d² = (Fintype.card n)²`. -/
noncomputable def hermitianOrthonormalBasis : Module.Basis (n × n) ℂ (Matrix n n ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank gellMann_linearIndependent
    (by rw [Fintype.card_prod, finrank_eq_card_sq, sq])

/-- Every member of the orthonormal Hermitian basis is Hermitian. -/
theorem hermitianOrthonormalBasis_isHermitian (p : n × n) :
    (hermitianOrthonormalBasis p).IsHermitian := sorry

/-- The orthonormal Hermitian basis is orthonormal under the Hilbert–Schmidt inner product. -/
theorem hermitianOrthonormalBasis_orthonormal (p q : n × n) :
    hsInner (hermitianOrthonormalBasis p) (hermitianOrthonormalBasis q) =
      if p = q then 1 else 0 := sorry

end HermitianBasis

end Matrix

end
