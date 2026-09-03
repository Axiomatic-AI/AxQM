/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EnsemblePurification
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.EntropyOrthogonalMixture
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedKleinInequality
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# AxQM — the equality condition in the N&C Thm 11.10 entropy bound

Nielsen & Chuang, Theorem 11.10, states the entropy-of-a-mixture bound
`S(∑ᵢ pᵢ ρᵢ) ≤ ∑ᵢ pᵢ S(ρᵢ) + H(p)` with equality **iff** the `ρᵢ` have support on
orthogonal subspaces.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **N&C Theorem 11.10, the equality condition.** For a mixture `μ = ∑ᵢ pᵢ ρᵢ` of quantum states,
the entropy-of-a-mixture upper bound `S(μ) ≤ H(p) + ∑ᵢ pᵢ S(ρᵢ)` (eq. (11.87)) holds with
**equality if and only if the components of non-zero probability have orthogonal supports**:

`S(∑ᵢ pᵢ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ) ↔ (∀ i ≠ j with pᵢ, pⱼ ≠ 0, (ρ i).op * (ρ j).op = 0)`.

The orthogonal-support condition is recorded as the vanishing operator product
`(ρ i).op * (ρ j).op = 0`, the intrinsic underlying operator form of
`(ρ i).support ⟂ (ρ j).support`. The `pᵢ, pⱼ ≠ 0` restriction is essential and
faithful: a probability-zero component contributes nothing to `μ` and nothing to the bound
(`0 · S(ρᵢ) = 0`, `η(0) = 0`), so its support is genuinely unconstrained — the *unrestricted*
pairwise condition would make the iff false (e.g. `p = (1, 0)` gives equality for every `ρ₂`).
-/
theorem State.vonNeumannEntropy_mix_eq_iff_orthogonal {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S) :
    (State.mix p hp hsum ρ).vonNeumannEntropy
        = Real.entropy p + ∑ i, p i * (ρ i).vonNeumannEntropy
      ↔ ∀ ⦃i j⦄, i ≠ j → p i ≠ 0 → p j ≠ 0 → (ρ i).op * (ρ j).op = 0 := sorry

end AxQM
