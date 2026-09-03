/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# AxQM — the pseudo-inverse `ρ⁻¹` of a density operator

Nielsen & Chuang, in Exercise 2.73, use the operator `ρ⁻¹`: the inverse of `ρ` regarded as acting
only on its support, the span of the eigenvectors of `ρ` with non-zero eigenvalues. Because a
density operator need not be
invertible on the whole space (it can have a kernel), this restricted inverse is the standard
**Moore–Penrose pseudo-inverse** of `ρ`.

## Main definitions

* `AxQM.State.pseudoInverse` — the pseudo-inverse `ρ⁻¹`.
-/

open scoped InnerProductSpace
open InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace State

/-- **The pseudo-inverse `ρ⁻¹` of a density operator**: the inverse
of `ρ` on its support, extended by zero on the kernel. Built from the spectral decomposition
`ρ = ∑ₖ λₖ |bₖ⟩⟨bₖ|` over the orthonormal eigenbasis `bₖ` by inverting each eigenvalue with the real
field inverse (so a zero eigenvalue stays `0`): `ρ⁻¹ = ∑ₖ λₖ⁻¹ |bₖ⟩⟨bₖ|`. -/
def pseudoInverse (ρ : State S) : S.space →L[ℂ] S.space :=
  ∑ k, (((ρ.isDensity.isSymmetric.eigenvalues rfl k)⁻¹ : ℝ) : ℂ) •
    rankOne ℂ (ρ.isDensity.isSymmetric.eigenvectorBasis rfl k)
      (ρ.isDensity.isSymmetric.eigenvectorBasis rfl k)

end State

end AxQM
