/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace

/-!
# AxQM.Basic.API — shared derived facts on the `PureState` primitive

* `PureState.normalize v hv` — the pure state `‖v‖⁻¹ • v` of a nonzero vector `v : S`.
* `PureState.overlap` — the **overlap** (transition amplitude) `⟨ψ|φ⟩` of two pure states.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

namespace PureState

variable {S : QSystem}

/-- The **overlap** (transition amplitude) `⟨ψ|φ⟩` of two pure states of the same system, `⟪ψ.vec,
φ.vec⟫`. Following Mathlib's `inner ℂ` convention it is conjugate-linear in the bra `ψ` and
linear in the ket `φ`; its magnitude `‖ψ.overlap φ‖` is the physical transition probability
amplitude. -/
def overlap (ψ φ : PureState S) : ℂ := inner ℂ ψ.vec φ.vec

/-- Unfolding lemma for `PureState.overlap`: `ψ.overlap φ = ⟪ψ.vec, φ.vec⟫`. -/
theorem overlap_def (ψ φ : PureState S) : ψ.overlap φ = inner ℂ ψ.vec φ.vec := rfl

/-- The **normalized pure state** `‖v‖⁻¹ • v` built from a nonzero vector `v : S`. -/
def normalize (v : S) (hv : v ≠ 0) : PureState S where
  vec := ((‖v‖ : ℝ) : ℂ)⁻¹ • v
  normalized := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

end PureState

end AxQM
