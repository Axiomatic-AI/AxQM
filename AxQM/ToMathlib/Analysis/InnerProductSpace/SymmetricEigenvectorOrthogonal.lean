/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Eigenvectors of a symmetric operator with distinct eigenvalues are orthogonal

Let `E` be an inner product space over `𝕜` (`ℝ` or `ℂ`). This file records that two eigenvectors of
a symmetric (self-adjoint, "Hermitian") operator belonging to different eigenvalues are necessarily
orthogonal — Nielsen & Chuang, Exercise 2.22.

## Main results

* `LinearMap.IsSymmetric.inner_eq_zero_of_hasEigenvector_of_ne`: two eigenvectors of a symmetric
  operator with distinct eigenvalues are orthogonal.
-/

@[expose] public section

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Nielsen & Chuang, Exercise 2.22.** Two eigenvectors of a symmetric (self-adjoint) operator `T`
belonging to *different* eigenvalues are orthogonal: if `T.IsSymmetric`, `v` is an eigenvector
with eigenvalue `μ`, `w` is an eigenvector with eigenvalue `ν`, and `μ ≠ ν`, then `⟪v, w⟫ = 0`.
-/
theorem inner_eq_zero_of_hasEigenvector_of_ne {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {μ ν : 𝕜}
    {v w : E} (hv : Module.End.HasEigenvector T μ v) (hw : Module.End.HasEigenvector T ν w)
    (hμν : μ ≠ ν) : inner 𝕜 v w = 0 := sorry

end LinearMap.IsSymmetric
