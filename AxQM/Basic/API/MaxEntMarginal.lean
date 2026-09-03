/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SchmidtNumber
import AxQM.Basic.API.Entropy

/-!
# AxQM — maximally entangled resource marginals

`State.IsMaxEntMarginal ρ K`: the state `ρ` is the reduced state (one-party marginal) of a
**maximally entangled pure state of Schmidt rank `K`** — equivalently, `ρ` is maximally mixed on a
`K`-dimensional subspace (its `K` non-zero eigenvalues are all `1/K`).
-/

noncomputable section

namespace AxQM

namespace State

variable {S : QSystem}

/-- `ρ.IsMaxEntMarginal K`: `ρ` is the marginal of a maximally entangled pure state of Schmidt rank
`K`, i.e. `ρ` is maximally mixed on a `K`-dimensional subspace. Characterised by its rank being
`K` and its entropy attaining the maximal value `log K` for that rank — which forces the `K`
non-zero eigenvalues to be uniform, each `1/K`. -/
def IsMaxEntMarginal (ρ : State S) (K : ℕ) : Prop :=
  ρ.rank = K ∧ ρ.vonNeumannEntropy = Real.log K

end State

end AxQM
