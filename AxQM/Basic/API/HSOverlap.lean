/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Purity

/-!
# AxQM.Basic.API — Hilbert–Schmidt overlap of two states

The **Hilbert–Schmidt (Frobenius) overlap** `tr(ρ σ)` of two density operators, as a real number.
It vanishes exactly when the two states have orthogonal supports.
-/

noncomputable section

open scoped InnerProductSpace

namespace AxQM

variable {S : QSystem}

/-- The **Hilbert–Schmidt (Frobenius) overlap** `tr(ρ σ)` of two states `ρ σ`, as a real number (`re
tr(ρ.op σ.op)`). It measures the (un-normalised) overlap of the two density operators: it
vanishes exactly when their supports are orthogonal. -/
def State.hsOverlap (ρ σ : State S) : ℝ :=
  RCLike.re (LinearMap.trace ℂ S ((ρ.op * σ.op : S →L[ℂ] S) : S →ₗ[ℂ] S))

end AxQM
