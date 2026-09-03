/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.NormalOperator

/-!
# The spectral theorem for self-adjoint (Hermitian) operators

An operator `T` on a finite-dimensional inner product space is *self-adjoint* (N&C: *Hermitian*)
when it equals its own adjoint. Mathlib spells this with the `IsSelfAdjoint` predicate
(`star T = T`); for `T : E →ₗ[𝕜] E` the `star` is the adjoint, so `IsSelfAdjoint T` is exactly
`Tᴴ = T`. This file proves the **spectral theorem** for such operators: `T` is self-adjoint if and
only if it is diagonal with respect to some orthonormal basis *with real eigenvalues*, i.e. there
is an orthonormal eigenbasis whose eigenvalues are real.

## Main results

* `LinearMap.isSelfAdjoint_iff_exists_orthonormalBasis_real`: the spectral theorem, packaging the
  two halves as an equivalence.
-/

public section

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **Spectral theorem for self-adjoint operators.** An operator `T` on a finite-dimensional inner
product space is self-adjoint (`IsSelfAdjoint T`, i.e. `Tᴴ = T`) if and only if it is diagonal with
respect to some orthonormal basis with real eigenvalues. This is the Hermitian case of N&C's
spectral decomposition (Theorem 2.1 / Box 2.2), and unlike the normal case it holds over any
`RCLike` field. -/
theorem isSelfAdjoint_iff_exists_orthonormalBasis_real {T : E →ₗ[𝕜] E} :
    IsSelfAdjoint T ↔
      ∃ (b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E) (μ : Fin (Module.finrank 𝕜 E) → ℝ),
        ∀ i, T (b i) = (μ i : 𝕜) • b i := sorry

end LinearMap

end
