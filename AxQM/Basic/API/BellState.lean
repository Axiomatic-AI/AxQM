/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Observable
import AxQM.Basic.API.Qubit

/-!
# AxQM.Basic.API — the Bell state Φ⁺

The maximally entangled two-qubit **Bell state** `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`, a `PureState` of the
composite system `qubit ⊗ qubit`. This is the canonical entangled state of Nielsen & Chuang §1.3.6 /
§2.3, used throughout Chapter 2 (superdense coding, the EPR/Bell exercises).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- The **unnormalised Bell vector** `|00⟩ + |11⟩` in the two-qubit state space
`qubit.space ⊗[ℂ] qubit.space`. -/
def bellVec : (qubit ⊗ qubit).space :=
  (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec

/-- **The squared norm of the unnormalised Bell vector is `2`:** `⟨β|β⟩ = 2`. -/
theorem bellVec_inner_self : (inner ℂ bellVec bellVec : ℂ) = 2 := by
  change (@inner ℂ (TensorProduct ℂ qubit.space qubit.space) _ bellVec bellVec : ℂ) = 2
  rw [bellVec, inner_add_left, inner_add_right, inner_add_right,
    TensorProduct.inner_tmul, TensorProduct.inner_tmul,
    TensorProduct.inner_tmul, TensorProduct.inner_tmul]
  simp only [qubitBasis_inner_qubitBasis]
  norm_num

/-- The **Bell state** `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`, the maximally entangled pure state of the
composite system `qubit ⊗ qubit`. -/
def bellPhiPlus : PureState (qubit ⊗ qubit) where
  vec := (Real.sqrt 2 : ℂ)⁻¹ • bellVec
  normalized := by
    have hb : ‖bellVec‖ = Real.sqrt 2 := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), bellVec_inner_self]; norm_num
    rw [norm_smul, hb, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), inv_mul_cancel₀ (by positivity)]

end AxQM
