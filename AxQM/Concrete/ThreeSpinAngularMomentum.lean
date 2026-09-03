/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concrete: three spin-½ total angular momentum eigenstates (Nielsen & Chuang, Exercise 7.27)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 7.27
("Three spin angular momenta states", p. 314) states that three spin-½ spins combine into
total-angular-momentum multiplets with `j = 3/2` and `j = 1/2`, and lists eight explicit
three-qubit states (7.98)–(7.105) forming a basis of simultaneous eigenvectors, with
`J²|j,mⱼ⟩ = j(j+1)|j,mⱼ⟩` and `jz|j,mⱼ⟩ = mⱼ|j,mⱼ⟩`.

## Main results
* `emb1`/`emb2`/`emb3`, `jx`/`jy`/`jz`, `jsq` — the single-qubit embeddings and the total-momentum
  operators, faithful to the exercise's definitions.
* `symP32`, `symP12`, `symM12`, `symM32` — the `j = 3/2` symmetric quartet (7.101), (7.100),
  (7.99), (7.98); `mixAP12`, `mixAM12` — the first `j = 1/2` doublet (7.102), (7.103); `mixBP12`,
  `mixBM12` — the second `j = 1/2` doublet (7.104), (7.105).
* `jz_*` (eight) — each state is a `jz`-eigenstate, with the **actual** eigenvalue.
* `jsq_*` (eight) — each state is a `J²`-eigenstate with eigenvalue `j(j+1)` (`15/4` or `3/4`).
-/

namespace AxQM.Concrete.ThreeSpin

open Matrix Complex
open scoped Kronecker

/-- The three-spin register index: a three-bit string `|abc⟩`, `a`/`b`/`c` the values of the three
qubits. The `2³ = 8`-dimensional state space of Exercise 7.27 is `Fin 2 × Fin 2 × Fin 2 → ℂ`. -/
abbrev Reg : Type := Fin 2 × Fin 2 × Fin 2

/-- Embed a single-qubit operator `A` on the **first** qubit: `A ⊗ I ⊗ I`, as a Kronecker product
(`⊗ₖ = Matrix.kroneckerMap (· * ·)`). -/
def emb1 (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Reg Reg ℂ :=
  A ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)

/-- Embed a single-qubit operator `A` on the **second** qubit: `I ⊗ A ⊗ I`. -/
def emb2 (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Reg Reg ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- Embed a single-qubit operator `A` on the **third** qubit: `I ⊗ I ⊗ A`. -/
def emb3 (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Reg Reg ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A)

/-- The total-momentum operator `jx = (X₁ + X₂ + X₃)/2` (N&C p. 314). -/
noncomputable def jx : Matrix Reg Reg ℂ := (2⁻¹ : ℂ) • (emb1 pauliX + emb2 pauliX + emb3 pauliX)

/-- The total-momentum operator `jy = (Y₁ + Y₂ + Y₃)/2` (N&C p. 314). -/
noncomputable def jy : Matrix Reg Reg ℂ := (2⁻¹ : ℂ) • (emb1 pauliY + emb2 pauliY + emb3 pauliY)

/-- The total-momentum operator `jz = (Z₁ + Z₂ + Z₃)/2` (N&C p. 314). -/
noncomputable def jz : Matrix Reg Reg ℂ := (2⁻¹ : ℂ) • (emb1 pauliZ + emb2 pauliZ + emb3 pauliZ)

/-- The total angular momentum squared `J² = jx² + jy² + jz²` (N&C eq. 7.97 for three spins). -/
noncomputable def jsq : Matrix Reg Reg ℂ := jx * jx + jy * jy + jz * jz

/-- The computational-basis ket `|abc⟩` as a column vector — the standard-basis indicator
`Pi.single (a,b,c) 1` at the register point `(a, b, c)`. -/
def ket (a b c : Fin 2) : Reg → ℂ := Pi.single (a, b, c) 1

/-- `j = 3/2` symmetric state with `jz = +3/2`: the ket `|000⟩`. N&C (7.101) prints this as
`|3/2,-3/2⟩` (opposite spin convention). -/
def symP32 : Reg → ℂ := ket 0 0 0

/-- `j = 3/2` symmetric state with `jz = +1/2`: `(|100⟩+|010⟩+|001⟩)/√3`. N&C (7.100) prints this as
`|3/2,-1/2⟩`. -/
noncomputable def symP12 : Reg → ℂ :=
  (Real.sqrt 3 : ℂ)⁻¹ • (ket 1 0 0 + ket 0 1 0 + ket 0 0 1)

/-- `j = 3/2` symmetric state with `jz = -1/2`: `(|011⟩+|101⟩+|110⟩)/√3`. N&C (7.99) prints this as
`|3/2,+1/2⟩`. -/
noncomputable def symM12 : Reg → ℂ :=
  (Real.sqrt 3 : ℂ)⁻¹ • (ket 0 1 1 + ket 1 0 1 + ket 1 1 0)

/-- `j = 3/2` symmetric state with `jz = -3/2`: the ket `|111⟩`. N&C (7.98) prints this as
`|3/2,+3/2⟩` (opposite spin convention). -/
def symM32 : Reg → ℂ := ket 1 1 1

/-- First `j = 1/2` doublet, upper state with `jz = +1/2`: `(-|001⟩+|100⟩)/√2`. N&C (7.102),
`|1/2,+1/2⟩₁` (label reproduced exactly). -/
noncomputable def mixAP12 : Reg → ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • (ket 1 0 0 - ket 0 0 1)

/-- First `j = 1/2` doublet, lower state with `jz = -1/2`: `(|110⟩-|011⟩)/√2`. N&C (7.103),
`|1/2,-1/2⟩₁`. -/
noncomputable def mixAM12 : Reg → ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • (ket 1 1 0 - ket 0 1 1)

/-- Second `j = 1/2` doublet, upper state with `jz = +1/2`: `(|001⟩-2|010⟩+|100⟩)/√6`. N&C (7.104),
`|1/2,+1/2⟩₂`. -/
noncomputable def mixBP12 : Reg → ℂ :=
  (Real.sqrt 6 : ℂ)⁻¹ • (ket 0 0 1 - (2 : ℂ) • ket 0 1 0 + ket 1 0 0)

/-- Second `j = 1/2` doublet, lower state with `jz = -1/2`: `(-|110⟩+2|101⟩-|011⟩)/√6`. N&C (7.105),
`|1/2,-1/2⟩₂`. -/
noncomputable def mixBM12 : Reg → ℂ :=
  (Real.sqrt 6 : ℂ)⁻¹ • ((2 : ℂ) • ket 1 0 1 - ket 1 1 0 - ket 0 1 1)

/-- `symP32 = |000⟩` is a `jz`-eigenstate with eigenvalue `+3/2` (N&C prints `|3/2,-3/2⟩`). -/
theorem jz_symP32 : jz *ᵥ symP32 = (3 / 2 : ℂ) • symP32 := sorry

/-- `symP12` is a `jz`-eigenstate with eigenvalue `+1/2` (N&C prints `|3/2,-1/2⟩`). -/
theorem jz_symP12 : jz *ᵥ symP12 = (1 / 2 : ℂ) • symP12 := sorry

/-- `symM12` is a `jz`-eigenstate with eigenvalue `-1/2` (N&C prints `|3/2,+1/2⟩`). -/
theorem jz_symM12 : jz *ᵥ symM12 = (-1 / 2 : ℂ) • symM12 := sorry

/-- `symM32 = |111⟩` is a `jz`-eigenstate with eigenvalue `-3/2` (N&C prints `|3/2,+3/2⟩`). -/
theorem jz_symM32 : jz *ᵥ symM32 = (-3 / 2 : ℂ) • symM32 := sorry

/-- `mixAP12` is a `jz`-eigenstate with eigenvalue `+1/2` (N&C `|1/2,+1/2⟩₁`). -/
theorem jz_mixAP12 : jz *ᵥ mixAP12 = (1 / 2 : ℂ) • mixAP12 := sorry

/-- `mixAM12` is a `jz`-eigenstate with eigenvalue `-1/2` (N&C `|1/2,-1/2⟩₁`). -/
theorem jz_mixAM12 : jz *ᵥ mixAM12 = (-1 / 2 : ℂ) • mixAM12 := sorry

/-- `mixBP12` is a `jz`-eigenstate with eigenvalue `+1/2` (N&C `|1/2,+1/2⟩₂`). -/
theorem jz_mixBP12 : jz *ᵥ mixBP12 = (1 / 2 : ℂ) • mixBP12 := sorry

/-- `mixBM12` is a `jz`-eigenstate with eigenvalue `-1/2` (N&C `|1/2,-1/2⟩₂`). -/
theorem jz_mixBM12 : jz *ᵥ mixBM12 = (-1 / 2 : ℂ) • mixBM12 := sorry

set_option maxHeartbeats 800000 in
-- `jsq = jx²+jy²+jz²` expands each matrix product into a sum over the 8-element register.
/-- `symP32` is a `J²`-eigenstate with eigenvalue `15/4 = (3/2)(3/2+1)`. -/
theorem jsq_symP32 : jsq *ᵥ symP32 = (15 / 4 : ℂ) • symP32 := sorry

set_option maxHeartbeats 800000 in
-- `jsq = jx²+jy²+jz²` expands each matrix product into a sum over the 8-element register.
/-- `symP12` is a `J²`-eigenstate with eigenvalue `15/4`. -/
theorem jsq_symP12 : jsq *ᵥ symP12 = (15 / 4 : ℂ) • symP12 := sorry

set_option maxHeartbeats 800000 in
-- `jsq = jx²+jy²+jz²` expands each matrix product into a sum over the 8-element register.
/-- `symM12` is a `J²`-eigenstate with eigenvalue `15/4`. -/
theorem jsq_symM12 : jsq *ᵥ symM12 = (15 / 4 : ℂ) • symM12 := sorry

set_option maxHeartbeats 800000 in
-- `jsq = jx²+jy²+jz²` expands each matrix product into a sum over the 8-element register.
/-- `symM32` is a `J²`-eigenstate with eigenvalue `15/4`. -/
theorem jsq_symM32 : jsq *ᵥ symM32 = (15 / 4 : ℂ) • symM32 := sorry

set_option maxHeartbeats 800000 in
-- `jsq = jx²+jy²+jz²` expands each matrix product into a sum over the 8-element register.
/-- `mixAP12` is a `J²`-eigenstate with eigenvalue `3/4 = (1/2)(1/2+1)`. -/
theorem jsq_mixAP12 : jsq *ᵥ mixAP12 = (3 / 4 : ℂ) • mixAP12 := sorry

set_option maxHeartbeats 800000 in
-- `jsq = jx²+jy²+jz²` expands each matrix product into a sum over the 8-element register.
/-- `mixAM12` is a `J²`-eigenstate with eigenvalue `3/4`. -/
theorem jsq_mixAM12 : jsq *ᵥ mixAM12 = (3 / 4 : ℂ) • mixAM12 := sorry

set_option maxHeartbeats 800000 in
-- `jsq = jx²+jy²+jz²` expands each matrix product into a sum over the 8-element register.
/-- `mixBP12` is a `J²`-eigenstate with eigenvalue `3/4`. -/
theorem jsq_mixBP12 : jsq *ᵥ mixBP12 = (3 / 4 : ℂ) • mixBP12 := sorry

set_option maxHeartbeats 800000 in
-- `jsq = jx²+jy²+jz²` expands each matrix product into a sum over the 8-element register.
/-- `mixBM12` is a `J²`-eigenstate with eigenvalue `3/4`. -/
theorem jsq_mixBM12 : jsq *ᵥ mixBM12 = (3 / 4 : ℂ) • mixBM12 := sorry

/-- Reinterpret a raw column vector `v : Reg → ℂ` as a Hilbert-space vector of
`EuclideanSpace ℂ Reg = PiLp 2 (fun _ : Reg => ℂ)` — the same underlying data, equipped with the
`ℓ²` inner product `⟨v|w⟩ = Σᵢ vᵢ* wᵢ` and norm used throughout N&C. -/
noncomputable def toEuclid (v : Reg → ℂ) : EuclideanSpace ℂ Reg := (WithLp.equiv 2 (Reg → ℂ)).symm v

/-- `toEuclid` is additive. -/
theorem toEuclid_add (u v : Reg → ℂ) : toEuclid (u + v) = toEuclid u + toEuclid v := rfl

/-- `toEuclid` respects subtraction. -/
theorem toEuclid_sub (u v : Reg → ℂ) : toEuclid (u - v) = toEuclid u - toEuclid v := rfl

/-- `toEuclid` is `ℂ`-linear in the scalar. -/
theorem toEuclid_smul (a : ℂ) (v : Reg → ℂ) : toEuclid (a • v) = a • toEuclid v := rfl

/-- The Hilbert-space image of a computational ket `|abc⟩` is the `ℓ²` standard-basis vector
`EuclideanSpace.single (a,b,c) 1`. -/
theorem toEuclid_ket (a b c : Fin 2) : toEuclid (ket a b c) = EuclideanSpace.single (a, b, c) 1 :=
  rfl

/-- Orthonormality of the `ℓ²` standard basis: `⟨e_p|e_q⟩ = δ_{pq}`. -/
theorem inner_single_single (p q : Reg) :
    (inner ℂ (EuclideanSpace.single p (1 : ℂ)) (EuclideanSpace.single q 1)) =
      if p = q then 1 else 0 := by
  rw [EuclideanSpace.inner_single_left, PiLp.single_apply]; simp

/-- The eight total-angular-momentum states (7.98)–(7.105) packaged as a family of Hilbert-space
vectors indexed by `Fin 8`: the `j = 3/2` symmetric quartet `symP32, symP12, symM12, symM32`,
followed by the two `j = 1/2` doublets `mixAP12, mixAM12` and `mixBP12, mixBM12`. -/
noncomputable def stateVec : Fin 8 → EuclideanSpace ℂ Reg :=
  ![toEuclid symP32, toEuclid symP12, toEuclid symM12, toEuclid symM32,
    toEuclid mixAP12, toEuclid mixAM12, toEuclid mixBP12, toEuclid mixBM12]

set_option maxHeartbeats 800000 in
-- 64 Gram-matrix entries (`fin_cases i <;> fin_cases j`) are discharged in one tactic block.
set_option linter.unusedSimpArgs false in
/-- **The eight states are orthonormal.** Each is a unit vector and distinct states are orthogonal
(N&C `⟨j,mⱼ|j',mⱼ'⟩ = δ`). -/
theorem stateVec_orthonormal : Orthonormal ℂ stateVec := by
  have e2 : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by rw [← Complex.ofReal_pow, Real.sq_sqrt] <;> norm_num
  have e3 : ((Real.sqrt 3 : ℂ)) ^ 2 = 3 := by rw [← Complex.ofReal_pow, Real.sq_sqrt] <;> norm_num
  have e6 : ((Real.sqrt 6 : ℂ)) ^ 2 = 6 := by rw [← Complex.ofReal_pow, Real.sq_sqrt] <;> norm_num
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [stateVec, Fin.reduceFinMk, Nat.reduceAdd, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Fin.isValue, symP32, symP12, symM12, symM32, mixAP12,
      mixAM12, mixBP12, mixBM12, toEuclid_ket, toEuclid_add, toEuclid_sub, toEuclid_smul,
      inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, inner_single_single, Prod.mk.injEq, Fin.reduceEq, and_true, true_and,
      and_false, false_and, and_self, if_true, if_false, reduceIte, map_ofNat, map_one,
      Complex.conj_ofReal, map_inv₀, mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
      sub_zero, zero_sub] <;>
    ring_nf <;> norm_num [inv_pow, e2, e3, e6]

/-- **Nielsen & Chuang, Exercise 7.27.** The eight total-angular-momentum states form a basis of
the three-qubit space `(ℂ²)⊗³`. -/
noncomputable def stateBasis : Module.Basis (Fin 8) ℂ (EuclideanSpace ℂ Reg) :=
  basisOfLinearIndependentOfCardEqFinrank stateVec_orthonormal.linearIndependent
    (by rw [finrank_euclideanSpace]; decide)

end AxQM.Concrete.ThreeSpin
