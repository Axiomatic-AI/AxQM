/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PseudoInverse
import AxQM.Basic.API.TypicalSubspace
import AxQM.Basic.API.Evolution
import AxQM.ToMathlib.Analysis.Convex.SameNonzero
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Basic.API — the same-non-zero-spectrum relation `ρ ≅ σ`

Nielsen & Chuang, Exercise 12.22, compares the eigenvalue distributions of density operators up to
their *non-zero* entries: writing `λ_ρ` for the spectrum of `ρ` (`State.eigenvalueDist`),
`λ_ρ ≅ λ_σ` means the two vectors have identical non-zero entries (equal up to a permutation and the
insertion/deletion of zeros). This file records that relation on states.

## Main definitions

* `State.SameNonzeroSpectrum ρ σ` : `SameNonzero λ_ρ λ_σ`, the state-level `≅`.
-/

namespace AxQM

variable {S T : QSystem}

/-- **Same non-zero spectrum** `ρ ≅ σ` (Nielsen & Chuang, Ex. 12.22, the `≅` relation on spectra):
the density operators `ρ` and `σ` — on possibly *different* systems `S` and `T` — have eigenvalue
distributions with identical non-zero entries. -/
def State.SameNonzeroSpectrum (ρ : State S) (σ : State T) : Prop :=
  SameNonzero ρ.eigenvalueDist σ.eigenvalueDist

end AxQM
