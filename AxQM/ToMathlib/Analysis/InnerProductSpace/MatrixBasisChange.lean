/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Matrix representations under a change of orthonormal basis

Let `E` be a finite-dimensional inner product space over `𝕜` (`RCLike 𝕜`) and let `A : E →ₗ[𝕜] E`
be an operator. Its matrix representation with respect to an orthonormal basis `v` is
`LinearMap.toMatrixOrthonormal v A`, whose entries are the inner products
`(LinearMap.toMatrixOrthonormal v A) i j = ⟪v i, A (v j)⟫`. This file records how that matrix
transforms when the basis is changed to another orthonormal basis `w` — Nielsen & Chuang,
Exercise 2.20.

## Main results

* `LinearMap.toMatrixOrthonormal_change_orthonormalBasis`: the two matrix representations of an
  operator with respect to two orthonormal bases are related by conjugation by the (unitary)
  change-of-basis matrix — the answer to N&C Exercise 2.20.
-/

@[expose] public section

open scoped Matrix

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι]

variable [DecidableEq ι] [FiniteDimensional 𝕜 E]

namespace LinearMap

/-- **Nielsen & Chuang, Exercise 2.20 (Basis changes).** The matrix representations of an operator
`A : E →ₗ[𝕜] E` with respect to two orthonormal bases `v` and `w` of a finite-dimensional inner
product space are related by conjugation by the change-of-basis matrix `U := w.toBasis.toMatrix
⇑v`:

`LinearMap.toMatrixOrthonormal w A = U * LinearMap.toMatrixOrthonormal v A * Uᴴ`.

Entrywise, `(LinearMap.toMatrixOrthonormal v A) i j = ⟪v i, A (v j)⟫` and `U i j = ⟪w i, v j⟫`,
so this is precisely N&C's `A'' = U A' U†` relating `A'ᵢⱼ = ⟨vᵢ|A|vⱼ⟩` and `A''ᵢⱼ = ⟨wᵢ|A|wⱼ⟩`.
The conjugating matrix `U` is unitary, so `Uᴴ = U⁻¹` and the relationship is a unitary similarity
transformation.
-/
theorem toMatrixOrthonormal_change_orthonormalBasis (v w : OrthonormalBasis ι 𝕜 E)
    (A : E →ₗ[𝕜] E) :
    toMatrixOrthonormal w A
      = w.toBasis.toMatrix ⇑v * toMatrixOrthonormal v A * (w.toBasis.toMatrix ⇑v)ᴴ := sorry

end LinearMap
