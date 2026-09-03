/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-!
# The spectral theorem for normal operators

An operator `T` on a finite-dimensional complex inner product space is *normal* when it commutes
with its adjoint. Mathlib spells this with the `IsStarNormal` predicate (`Commute (star T) T`);
for `T : E →ₗ[ℂ] E` the `star` is `LinearMap.adjoint`, so `IsStarNormal T` is exactly
`Tᴴ * T = T * Tᴴ`. This file proves the **spectral theorem** for such operators: `T` is normal
if and only if it is diagonal with respect to some orthonormal basis, i.e. there is an
orthonormal eigenbasis.

## Main results

* `LinearMap.isStarNormal_iff_exists_orthonormalBasis`: the spectral theorem.
-/

public section

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Spectral theorem for normal operators.** An operator `T` on a finite-dimensional complex
inner product space is normal (`IsStarNormal T`, i.e. it commutes with its adjoint) if and only if
it is diagonal with respect to some orthonormal basis. -/
theorem isStarNormal_iff_exists_orthonormalBasis {T : E →ₗ[ℂ] E} :
    IsStarNormal T ↔
      ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (μ : Fin (Module.finrank ℂ E) → ℂ),
        ∀ i, T (b i) = μ i • b i := sorry

end LinearMap

end
