/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Componentwise conjugation on `EuclideanSpace`

`EuclideanSpace.conjVec`: componentwise complex conjugation on `EuclideanSpace 𝕜 ι`,
antilinear over `𝕜` for `𝕜 = ℂ`, norm-preserving and involutive. Reduces to the identity
for real `𝕜`.
-/

@[expose] public section

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}

namespace EuclideanSpace

/-- Componentwise complex conjugation on `EuclideanSpace 𝕜 ι`. Antilinear over `𝕜`
(for `𝕜 = ℂ`), norm-preserving, and sesquilinear-conjugate on inner products. For real
`𝕜`, this reduces to the identity. -/
def conjVec (v : EuclideanSpace 𝕜 ι) : EuclideanSpace 𝕜 ι :=
  WithLp.toLp 2 (fun j ↦ star (v j))

@[simp]
theorem conjVec_apply (v : EuclideanSpace 𝕜 ι) (j : ι) :
    conjVec v j = star (v j) := by
  simp [conjVec]

/-- Componentwise conjugation on the coordinate track: `(conjVec v).ofLp = star v.ofLp`. -/
@[simp]
theorem ofLp_conjVec (v : EuclideanSpace 𝕜 ι) : (conjVec v).ofLp = star v.ofLp := by
  funext j; rw [conjVec_apply]; rfl

theorem conjVec_sum {ι' : Type*} (s : Finset ι') (g : ι' → EuclideanSpace 𝕜 ι) :
    conjVec (∑ k ∈ s, g k) = ∑ k ∈ s, conjVec (g k) := by
  ext j; simp [conjVec_apply, Finset.sum_apply, star_sum]

end EuclideanSpace
