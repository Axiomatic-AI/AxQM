/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Ensemble
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# AxQM — unitary freedom in the ensemble (machinery)

This file is the machinery behind **Nielsen–Chuang Theorem 2.6** ("unitary freedom
in the ensemble for density matrices"). The theorem answers: *which ensembles give rise to the same
density operator?* Following N&C, it is convenient to absorb the probabilities into the vectors,
working with the **subnormalized vectors** `|ψ̃ᵢ⟩ = √pᵢ |ψᵢ⟩` (eq. between (2.165) and (2.166)); an
ensemble `{pᵢ, |ψᵢ⟩}` then "generates" the density operator `ρ = ∑ᵢ |ψ̃ᵢ⟩⟨ψ̃ᵢ|`, since
`√pᵢ · conj(√pᵢ) = pᵢ`.

## Main definitions

* `AxQM.Ensemble.tildeVec` — the subnormalized vectors `√pᵢ • |ψᵢ⟩` of an ensemble.
* `AxQM.Ensemble.UnitarilyRelated` — the relation "same size, and the subnormalized
  vectors are related by a unitary coefficient matrix" (N&C eq. (2.167)).
-/

open scoped InnerProductSpace
open InnerProductSpace Finset

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Ensemble

/-- The **subnormalized vectors** `|ψ̃ᵢ⟩ = √pᵢ |ψᵢ⟩` of an ensemble `{pᵢ, |ψᵢ⟩}` (Nielsen–Chuang,
between eqs. (2.165) and (2.166)): the pure-state vectors scaled by the square roots of their
probabilities. The ensemble's density operator `ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` is exactly the sum of the
rank-one projectors of these vectors, `∑ᵢ |ψ̃ᵢ⟩⟨ψ̃ᵢ|`, because `√pᵢ · conj(√pᵢ) = pᵢ`. -/
def tildeVec (e : Ensemble S) (i : Fin e.card) : S.space :=
  (Real.sqrt (e.prob i) : ℂ) • (e.states i).vec

/-- **Unitary freedom relation** on ensembles (Nielsen–Chuang Theorem 2.6, eq. (2.167)): two
ensembles `e`, `f` are unitarily related when they have the **same size** (`e.card = f.card` —
the "padded" form: pad the smaller ensemble with probability-zero entries) and their
subnormalized vectors are related by a unitary coefficient matrix `u`, `√pᵢ|ψᵢ⟩ = ∑ⱼ uᵢⱼ
√qⱼ|φⱼ⟩`. -/
def UnitarilyRelated (e f : Ensemble S) : Prop :=
  ∃ (h : e.card = f.card) (u : Matrix (Fin e.card) (Fin e.card) ℂ),
    u ∈ Matrix.unitaryGroup (Fin e.card) ℂ ∧
      ∀ i, e.tildeVec i = ∑ j, u i j • f.tildeVec (Fin.cast h j)

end Ensemble

end AxQM
