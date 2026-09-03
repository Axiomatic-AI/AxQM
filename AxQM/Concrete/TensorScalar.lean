/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# AxQM.Concrete — scalar pull-through for threefold tensors

Elementary module-algebra facts that pull the scalars off individual factors of a threefold
tensor `x ⊗ (y ⊗ z)` out to the front. Position-explicit names spell out which slots carry a
scalar (`smul`) versus which are plain (`tmul`).
-/

open scoped TensorProduct

namespace AxQM.Concrete

variable {R E F G : Type*} [CommRing R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [AddCommGroup G] [Module R G]

/-- Scalar extraction for a threefold tensor with scalars on the **first two** factors:
`(c₁ • x) ⊗ (c₂ • y) ⊗ z = (c₁ c₂) • (x ⊗ y ⊗ z)`. -/
theorem smul_tmul_smul_tmul_left (c1 c2 : R) (x : E) (y : F) (z : G) :
    (c1 • x) ⊗ₜ[R] ((c2 • y) ⊗ₜ[R] z) = (c1 * c2) • (x ⊗ₜ[R] (y ⊗ₜ[R] z)) := by
  rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]

/-- Scalar extraction for a threefold tensor with scalars on the **last two** factors:
`x ⊗ (c₂ • y) ⊗ (c₃ • z) = (c₂ c₃) • (x ⊗ y ⊗ z)`. -/
theorem tmul_smul_tmul_smul_right (c2 c3 : R) (x : E) (y : F) (z : G) :
    x ⊗ₜ[R] ((c2 • y) ⊗ₜ[R] (c3 • z)) = (c2 * c3) • (x ⊗ₜ[R] (y ⊗ₜ[R] z)) := by
  rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.tmul_smul,
    TensorProduct.tmul_smul, smul_smul]

end AxQM.Concrete
