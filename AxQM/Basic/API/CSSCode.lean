/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.CosetDensityState
import AxQM.Basic.API.PureState
import AxQM.ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl
import AxQM.ToMathlib.InformationTheory.Coding.DualCodeCharacterSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# The bit-vector register and Pauli strings for CSS codes

This file sets up the ingredients used to build **CSS codes** (Nielsen & Chuang, §10.4.2) and to
compare them, over the register of `n`-qubit computational-basis states indexed by bit vectors
`ι → ZMod 2`.
-/

namespace AxQM

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- The **bit-vector register** for CSS codes: the group quantum system on the additive group of
bit vectors `ι → ZMod 2`, i.e. the `n`-qubit register (`n = #ι`) with computational basis `{|w⟩}`
indexed by bit strings `w : ι → ZMod 2`. -/
@[reducible] noncomputable def bitReg : QSystem := groupSystem (ι → ZMod 2)

variable (ι) in
/-- The **computational orthonormal basis** `{|w⟩}` of the register `bitReg ι`, the standard
Euclidean basis indexed by bit vectors. -/
noncomputable def regBasis : OrthonormalBasis (ι → ZMod 2) ℂ (bitReg ι).space :=
  EuclideanSpace.basisFun (ι → ZMod 2) ℂ

/-- The **computational basis pure state** `|w⟩` of the register `bitReg ι`, for a bit vector
`w : ι → ZMod 2`. -/
noncomputable def regBasisState (w : ι → ZMod 2) : PureState (bitReg ι) where
  vec := regBasis ι w
  normalized := (regBasis ι).orthonormal.1 w

@[simp]
theorem regBasisState_vec (w : ι → ZMod 2) : (regBasisState w).vec = regBasis ι w := rfl

/-- The **Pauli bit-flip string** `X^v = X^{v₁} ⊗ ⋯ ⊗ X^{vₙ}` as a unitary `Evolution` of the
register `bitReg ι`. -/
noncomputable def bitString (v : ι → ZMod 2) : Evolution (bitReg ι) :=
  Evolution.ofLinearIsometryEquiv ((regBasis ι).equiv (regBasis ι) (Equiv.addRight v))

/-- The **Pauli phase-flip string** `Z^u = Z^{u₁} ⊗ ⋯ ⊗ Z^{uₙ}` as a unitary `Evolution` of the
register `bitReg ι`: the diagonal sign operator `|w⟩ ↦ (-1)^{u·w} |w⟩`, with the binary-code
character `(-1)^{(u·w).val}` on the diagonal. -/
noncomputable def phaseString (u : ι → ZMod 2) : Evolution (bitReg ι) where
  op := (regBasis ι).diagonalOperator fun w => (-1 : ℂ) ^ (u ⬝ᵥ w).val
  unitary := (regBasis ι).diagonalOperator_mem_unitary _ fun w => by
    rw [norm_pow, norm_neg, norm_one, one_pow]

/-- **The operator of a phase-flip string is the diagonal sign operator** on `regBasis`: `(Z^u).op =
diag_{regBasis} ((-1)^{u·w})`. -/
theorem phaseString_op (u : ι → ZMod 2) :
    (phaseString u).op = (regBasis ι).diagonalOperator (fun w => (-1 : ℂ) ^ (u ⬝ᵥ w).val) := rfl

/-- **Action of the phase-flip string on the computational basis**: `Z^u |w⟩ = (-1)^{u·w} |w⟩`. -/
theorem phaseString_op_regBasisState_vec (u w : ι → ZMod 2) :
    (phaseString u).op (regBasisState w).vec
      = (-1 : ℂ) ^ (u ⬝ᵥ w).val • (regBasisState w).vec := by
  simp only [regBasisState_vec, phaseString]
  exact (regBasis ι).diagonalOperator_apply_self _ w

/-- **Action of the phase-flip string on a raw basis vector**: `Z^u |w⟩ = (-1)^{u·w} |w⟩`. -/
theorem phaseString_op_regBasis (u w : ι → ZMod 2) :
    (phaseString u).op (regBasis ι w) = (-1 : ℂ) ^ (u ⬝ᵥ w).val • regBasis ι w := by
  have h := phaseString_op_regBasisState_vec (ι := ι) u w
  simpa only [regBasisState_vec] using h

/-- **Norm of a unit-modulus superposition of distinct computational basis states is one.** If
`idx : n → (ι → ZMod 2)` is injective — so the basis vectors `|idx i⟩` are orthonormal — and every
coefficient `coeff i` has unit modulus, then the normalized superposition
`|n|^{-1/2} ∑ᵢ coeff i |idx i⟩` is a unit vector. -/
private theorem norm_smul_sum_regBasis {n : Type*} [Fintype n] (hpos : 0 < Nat.card n)
    (idx : n → (ι → ZMod 2)) (hidx : Function.Injective idx)
    (coeff : n → ℂ) (hc : ∀ i, ‖coeff i‖ = 1) :
    ‖(Real.sqrt (Nat.card n) : ℂ)⁻¹ • ∑ i, coeff i • regBasis ι (idx i)‖ = 1 := by
  have horth : Orthonormal ℂ (fun i => regBasis ι (idx i)) :=
    (regBasis ι).orthonormal.comp idx hidx
  have hsq : ‖∑ i, coeff i • regBasis ι (idx i)‖ ^ 2 = (Nat.card n : ℝ) := by
    rw [horth.norm_sum_smul_sq coeff Finset.univ]
    simp only [hc, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  have hS : ‖∑ i, coeff i • regBasis ι (idx i)‖ = Real.sqrt (Nat.card n) := by
    rw [← hsq]; exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [norm_smul, hS, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hpos))]

variable (C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)]

/-- The **standard CSS coset state** `|x + C₂⟩ = |C₂|^{-1/2} ∑_{y ∈ C₂} |x + y⟩` (Nielsen & Chuang,
eq. 10.64), as a `PureState` of the register `bitReg ι`. The state depends only on the coset
`x + C₂`; the code `CSS(C₁, C₂)` is the span of these over `x ∈ C₁`. -/
noncomputable def cssStdState (x : ι → ZMod 2) : PureState (bitReg ι) where
  vec := (Real.sqrt (Nat.card ↥C₂) : ℂ)⁻¹ • ∑ y : ↥C₂, regBasis ι (x + (y : ι → ZMod 2))
  normalized := by
    have hpos : 0 < Nat.card ↥C₂ := by
      haveI : Nonempty ↥C₂ := ⟨⟨0, C₂.zero_mem⟩⟩; exact Nat.card_pos
    have hinj : Function.Injective (fun y : ↥C₂ => x + (y : ι → ZMod 2)) := fun a b hab =>
      Subtype.ext (add_left_cancel hab)
    have h := norm_smul_sum_regBasis hpos
      (fun y : ↥C₂ => x + (y : ι → ZMod 2)) hinj (fun _ => 1) (fun _ => norm_one)
    simpa only [one_smul] using h

@[simp]
theorem cssStdState_vec (x : ι → ZMod 2) :
    (cssStdState C₂ x).vec
      = (Real.sqrt (Nat.card ↥C₂) : ℂ)⁻¹ • ∑ y : ↥C₂, regBasis ι (x + (y : ι → ZMod 2)) := rfl

/-- The **twisted CSS coset state** `|x + C₂⟩_{u,v} = |C₂|^{-1/2} ∑_{y ∈ C₂} (-1)^{u·y} |x + y + v⟩`
(Nielsen & Chuang, eq. 10.75), as a `PureState` of `bitReg ι`. The family over `x ∈ C₁` spans the
twisted code `CSSᵤ,ᵥ(C₁, C₂)`. -/
noncomputable def cssTwistedState (u v x : ι → ZMod 2) : PureState (bitReg ι) where
  vec := (Real.sqrt (Nat.card ↥C₂) : ℂ)⁻¹ •
    ∑ y : ↥C₂, (-1 : ℂ) ^ (u ⬝ᵥ (y : ι → ZMod 2)).val •
      regBasis ι (x + (y : ι → ZMod 2) + v)
  normalized := by
    have hpos : 0 < Nat.card ↥C₂ := by
      haveI : Nonempty ↥C₂ := ⟨⟨0, C₂.zero_mem⟩⟩; exact Nat.card_pos
    have hinj : Function.Injective (fun y : ↥C₂ => x + (y : ι → ZMod 2) + v) := fun a b hab =>
      Subtype.ext (add_left_cancel (add_right_cancel hab))
    exact norm_smul_sum_regBasis hpos
      (fun y : ↥C₂ => x + (y : ι → ZMod 2) + v) hinj
      (fun y => (-1 : ℂ) ^ (u ⬝ᵥ (y : ι → ZMod 2)).val)
      (fun _ => by rw [norm_pow, norm_neg, norm_one, one_pow])

@[simp]
theorem cssTwistedState_vec (u v x : ι → ZMod 2) :
    (cssTwistedState C₂ u v x).vec
      = (Real.sqrt (Nat.card ↥C₂) : ℂ)⁻¹ •
        ∑ y : ↥C₂, (-1 : ℂ) ^ (u ⬝ᵥ (y : ι → ZMod 2)).val •
          regBasis ι (x + (y : ι → ZMod 2) + v) := rfl

end AxQM
