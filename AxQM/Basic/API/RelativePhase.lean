/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Qubit
import AxQM.Concrete.PauliEigenvectors
import AxQM.Concrete.PlusStateTensorPower
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# AxQM.Basic.API — the `|±⟩` states and relative-phase equivalence in a basis

**Nielsen & Chuang, Exercise 2.65** (§2.2.7, *Phase*,
p. 93). The exercise asks to express `|+⟩ = (|0⟩ + |1⟩)/√2` and `|-⟩ = (|0⟩ - |1⟩)/√2` in a
basis in which they are *not* the same up to a relative phase shift.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- Two pure states `ψ`, `φ` of a system `S` **differ by a relative phase in the frame `e`** (a
family of pure states, intended to be an orthonormal basis) if each amplitude of `ψ` equals
`exp(iθ)` times the corresponding amplitude of `φ`, for some real phase `θ` that may depend on the
index. This is Nielsen & Chuang's basis-dependent notion of relative phase (§2.2.7): the amplitude
of a state in direction `e i` is the inner product `⟪(e i).vec, ·.vec⟫`, and the phase `θ` is
allowed to vary from index to index. -/
def PureState.RelativePhaseEquiv {S : QSystem} {ι : Type*} (e : ι → PureState S)
    (ψ φ : PureState S) : Prop :=
  ∀ i, ∃ θ : ℝ, ⟪(e i).vec, ψ.vec⟫_ℂ = Complex.exp ((θ : ℂ) * Complex.I) • ⟪(e i).vec, φ.vec⟫_ℂ

/-- The **`X`-eigenstate `|+⟩ = (|0⟩ + |1⟩)/√2`** as a pure state of the qubit, built on the
concrete unit vector `Concrete.xPlus = (1/√2, 1/√2)`. -/
def qubitPlus : PureState qubit where
  vec := WithLp.toLp 2 Concrete.xPlus
  normalized := by
    have h : ‖(WithLp.toLp 2 Concrete.xPlus : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Concrete.xPlus_apply, Fin.sum_univ_two, Concrete.norm_invSqrt2_sq]
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, Real.sqrt_one]
    exact h

/-- The **`X`-eigenstate `|-⟩ = (|0⟩ - |1⟩)/√2`** as a pure state of the qubit, built on the
concrete unit vector `Concrete.xMinus = (1/√2, -1/√2)`. -/
def qubitMinus : PureState qubit where
  vec := WithLp.toLp 2 Concrete.xMinus
  normalized := by
    have h : ‖(WithLp.toLp 2 Concrete.xMinus : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Concrete.xMinus, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, norm_neg, Concrete.norm_invSqrt2_sq]
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, Real.sqrt_one]
    exact h

/-- The **`Y`-eigenstate `|+i⟩ = (|0⟩ + i|1⟩)/√2`** as a pure state of the qubit, built on the
concrete unit vector `Concrete.yPlus = (1/√2, i/√2)`. -/
def qubitPlusI : PureState qubit where
  vec := WithLp.toLp 2 Concrete.yPlus
  normalized := by
    have h : ‖(WithLp.toLp 2 Concrete.yPlus : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Concrete.yPlus, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        norm_mul, Complex.norm_I, mul_one, Concrete.norm_invSqrt2_sq]
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, Real.sqrt_one]
    exact h

/-- The **`Y`-eigenstate `|-i⟩ = (|0⟩ - i|1⟩)/√2`** as a pure state of the qubit, built on the
concrete unit vector `Concrete.yMinus = (1/√2, -i/√2)`. -/
def qubitMinusI : PureState qubit where
  vec := WithLp.toLp 2 Concrete.yMinus
  normalized := by
    have h : ‖(WithLp.toLp 2 Concrete.yMinus : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Concrete.yMinus, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        norm_neg, norm_mul, Complex.norm_I, mul_one, Concrete.norm_invSqrt2_sq]
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, Real.sqrt_one]
    exact h

end AxQM
