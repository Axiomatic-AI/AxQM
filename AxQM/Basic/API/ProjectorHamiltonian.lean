/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution
import AxQM.ToMathlib.Analysis.Normed.Algebra.ExponentialInvolution

/-!
# AxQM.Basic.API — the projector Hamiltonian

The rank-one *projector Hamiltonian* `H = |ψ⟩⟨ψ|` of Nielsen & Chuang, §6.2.

## Main declarations
* `AxQM.PureState.projObservable ψ` — the projector Hamiltonian `|ψ⟩⟨ψ|` packaged as an
  `Observable`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The projector Hamiltonian** `H = |ψ⟩⟨ψ|` of a pure state `ψ`, as an `Observable`. Nielsen &
Chuang, §6.2, takes `H = |x⟩⟨x| + |ψ⟩⟨ψ|` (eq. 6.18), a sum of two such projectors. -/
def PureState.projObservable (ψ : PureState S) : Observable S where
  op := rankOne ℂ ψ.vec ψ.vec
  selfAdjoint := by rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]

end AxQM
