/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SchmidtNumber
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# AxQM — the support of a density operator

Nielsen & Chuang, in Exercise 2.73, work with the **support** of a density operator `ρ`: the span
of its eigenvectors with non-zero eigenvalue (stated there for a Hermitian operator `A`, as the
span of its non-kernel eigenvectors).
Equivalently — and this is the definition we take — the support is the **range** of `ρ`, and, since
`ρ` is self-adjoint, the **orthogonal complement of its kernel**:
`support ρ = range ρ = (ker ρ)ᗮ`.

## Main definitions

* `AxQM.State.support` — the support `range ρ` of a density operator, a `Submodule`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace State

/-- **The support of a density operator**. Defined as `range ρ` so
that the rank identity `finrank (support ρ) = ρ.rank` is definitional. -/
def support (ρ : State S) : Submodule ℂ S.space :=
  LinearMap.range (ρ.op : S.space →ₗ[ℂ] S.space)

end State

end AxQM
