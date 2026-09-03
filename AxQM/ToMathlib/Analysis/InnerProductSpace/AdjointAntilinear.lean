/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Anti-linearity of the adjoint operation

Let `E`, `F` be finite-dimensional inner product spaces over `𝕜` (`ℝ` or `ℂ`). This file records
that the adjoint operation `A ↦ Aᴴ` on operators `E →ₗ[𝕜] F` is *anti-linear* (conjugate-linear):
it is additive and takes a scalar out with complex conjugation.

## Main results

* `LinearMap.adjoint_sum_smul`:
  `adjoint (∑ i ∈ s, a i • A i) = ∑ i ∈ s, star (a i) • adjoint (A i)`.
-/

@[expose] public section

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Nielsen & Chuang, Exercise 2.14 (anti-linearity of the adjoint), eq. (2.33).** The adjoint
operation is anti-linear: for a finite family of scalars `a i` and operators `A i` between
finite-dimensional inner product spaces, `adjoint (∑ i ∈ s, a i • A i) = ∑ i ∈ s, star (a i) •
adjoint (A i)`.

The conjugation `star (a i)` on the right (rather than `a i`) is what makes the operation
anti-linear rather than linear.
-/
theorem adjoint_sum_smul {ι : Type*} (s : Finset ι) (a : ι → 𝕜) (A : ι → (E →ₗ[𝕜] F)) :
    adjoint (∑ i ∈ s, a i • A i) = ∑ i ∈ s, star (a i) • adjoint (A i) := sorry

end LinearMap
