/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SubsystemErrorCorrection

/-!
# AxQM.Basic.API — the maximally-mixed code purification

**Nielsen & Chuang, Exercise 12.14** (p. 567). An `[n, k]` code `C` in a system `Q` with
orthonormal codewords `|x⟩` and code projector `P` has maximally-mixed code state `P / 2ᵏ`, which
N&C purify to a pure state of `R ⊗ Q`.
-/

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

variable {R A B : Type*}
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [FiniteDimensional ℂ R]
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]
  {ι : Type*} [Fintype ι]

/-- The (unnormalized) **maximally-entangled code purification vector** `|RQ⟩ = ∑ₓ eₓ ⊗ wₓ` in
`R ⊗ (A ⊗ B)`, for a reference family `e : ι → R` and codewords `w : ι → A ⊗ B`. Nielsen & Chuang's
`(1 / √2ᵏ) ∑ₓ |x⟩ ⊗ |x⟩` (Eq. (12.142)); the scalar `1 / √2ᵏ = 1 / √(card ι)` normalisation is
carried by the caller (it multiplies the density operator `|RQ⟩⟨RQ|` by `1 / card ι`). -/
def codePurifyVec (e : ι → R) (w : ι → A ⊗[ℂ] B) : R ⊗[ℂ] (A ⊗[ℂ] B) :=
  ∑ x, e x ⊗ₜ[ℂ] w x

end AxQM
