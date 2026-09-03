/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SchmidtDecomposition
import AxQM.Basic.API.PureState
import AxQM.Basic.API.Qubit
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# AxQM — the Schmidt decomposition of the entangled state `(|00⟩ + |01⟩ + |10⟩)/√3`

The third state of Nielsen & Chuang, Exercise 2.79: **genuinely entangled**, with *irrational*
Schmidt coefficients.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- The **unnormalised vector** `|00⟩ + |01⟩ + |10⟩` in the two-qubit state space
`qubit.space ⊗[ℂ] qubit.space`; its norm is `√3`. -/
def entangledThreeVec : (qubit ⊗ qubit).space :=
  (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec + (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 1).vec
    + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec

/-- **The squared norm of `|00⟩ + |01⟩ + |10⟩` is `3`:** `⟨ψ|ψ⟩ = 3`. -/
theorem entangledThreeVec_inner_self : (inner ℂ entangledThreeVec entangledThreeVec : ℂ) = 3 := by
  change (@inner ℂ (TensorProduct ℂ qubit.space qubit.space) _
    entangledThreeVec entangledThreeVec : ℂ) = 3
  simp only [entangledThreeVec, inner_add_left, inner_add_right, TensorProduct.inner_tmul,
    qubitBasis_inner_qubitBasis]
  norm_num

/-- **The norm of `|00⟩ + |01⟩ + |10⟩` is `√3`.** -/
theorem entangledThreeVec_norm : ‖entangledThreeVec‖ = Real.sqrt 3 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), entangledThreeVec_inner_self]; norm_num

/-- The unnormalised state vector is **nonzero**. -/
theorem entangledThreeVec_ne_zero : entangledThreeVec ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [entangledThreeVec_norm]; positivity)

/-- The **state** `(|00⟩ + |01⟩ + |10⟩)/√3`, a genuinely entangled pure state of `qubit ⊗ qubit`,
the normalisation of the vector `entangledThreeVec`. -/
def entangledThreeState : PureState (qubit ⊗ qubit) :=
  PureState.normalize entangledThreeVec entangledThreeVec_ne_zero

/-- The single-qubit vector `s|0⟩ + |1⟩` (i.e. `(s, 1)`) for a real `s`. -/
def entangledThreeEvec (s : ℝ) : qubit.space :=
  (s : ℂ) • (qubitBasis 0).vec + (qubitBasis 1).vec

/-- The **normalised Schmidt vector** `(s, 1)/‖(s, 1)‖`. At `s = φ` and `s = ψ` these are the
orthonormal Schmidt bases of `entangledThreeState`. -/
def entangledThreeSchmidtVec (s : ℝ) : qubit.space :=
  (‖entangledThreeEvec s‖ : ℂ)⁻¹ • entangledThreeEvec s

/-- **Nielsen & Chuang, Exercise 2.79 (state 3).** The genuinely entangled two-qubit state `(|00⟩ +
|01⟩ + |10⟩)/√3` (`entangledThreeState`) has the Schmidt decomposition with the two
**irrational** Schmidt coefficients `√((3+√5)/6)` and `√((3−√5)/6)`, and Schmidt bases
`(φ,1)/‖·‖`, `(ψ,1)/‖·‖`. The right basis carries the extra
sign `(ψ,1) ↦ −(ψ,1)`, folding the negative eigenvalue `ψ = (1−√5)/2` of the coefficient matrix
into a positive Schmidt coefficient. -/
theorem entangledThree_isSchmidtDecomposition :
    entangledThreeState.IsSchmidtDecomposition
      ![Real.sqrt ((3 + Real.sqrt 5) / 6), Real.sqrt ((3 - Real.sqrt 5) / 6)]
      ![entangledThreeSchmidtVec Real.goldenRatio, entangledThreeSchmidtVec Real.goldenConj]
      ![entangledThreeSchmidtVec Real.goldenRatio, -entangledThreeSchmidtVec Real.goldenConj] :=
        sorry

end AxQM
