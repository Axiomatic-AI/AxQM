/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-!
# Simultaneous diagonalisation of commuting symmetric operators

## Main results

* `LinearMap.IsSymmetric.commute_iff_exists_orthonormalBasis_forall_apply_eq_smul`: two
  symmetric operators on a finite-dimensional inner product space commute if and only if
  some single orthonormal basis diagonalises both.

-/

@[expose] public section

namespace LinearMap.IsSymmetric

section
open Module.End
open Module.End Submodule
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}

/-- **Simultaneous diagonalization theorem** (Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Theorem 2.2). Two symmetric operators `A` and `B` on a finite-dimensional inner
product space commute if and only if there is an orthonormal basis of common eigenvectors — an
orthonormal basis with respect to which both `A` and `B` are diagonal. (Over `𝕜 = ℂ`, `IsSymmetric`
is Hermiticity, recovering the textbook statement.) -/
theorem commute_iff_exists_orthonormalBasis_forall_apply_eq_smul
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    Commute A B ↔ ∃ b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E,
      (∀ i, ∃ μ : 𝕜, A (b i) = μ • b i) ∧ ∀ i, ∃ ν : 𝕜, B (b i) = ν • b i := sorry

end

end LinearMap.IsSymmetric
