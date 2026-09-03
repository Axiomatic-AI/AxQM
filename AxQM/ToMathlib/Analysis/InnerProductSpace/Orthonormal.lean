/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# The norm of a finite combination of orthonormal vectors

## Main results

* `Orthonormal.norm_sum_smul_sq`: `‖∑ i, a i • v i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2` for an orthonormal
  family `v`.

-/

@[expose] public section

noncomputable section
open RCLike Real Filter Module Topology ComplexConjugate Finsupp
open LinearMap (BilinForm)
variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable {ι : Type*} (𝕜)
variable {𝕜}

/-- **Pythagorean theorem (orthonormal-smul form)**: the squared norm of a finite linear
combination over an orthonormal family equals the sum of squared coefficient norms. -/
protected theorem Orthonormal.norm_sum_smul_sq {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜)
    (s : Finset ι) : ‖∑ i ∈ s, l i • v i‖ ^ 2 = ∑ i ∈ s, ‖l i‖ ^ 2 := by
  rw [← @inner_self_eq_norm_sq 𝕜, hv.inner_sum l l, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RCLike.conj_mul]
  norm_cast

end
