/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CommutingObservables
import AxQM.Basic.API.Eigenstate
import AxQM.Basic.API.ProjectiveMeasurement
import AxQM.Basic.Measurement
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Nielsen & Chuang, Exercise 12.33 (commuting observables obey classical probability)

*(N&C p. 597.)*

Commuting measurement observables [M_i,M_j]=0 obey classical probability arguments.

* `commuting_observables_classicalProbability` — a family of pairwise-commuting observables admits
  a single joint measurement whose classical distribution reproduces every member's quantum
  statistics.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Exercise 12.33.** Commuting measurement observables obey classical probability arguments.

Given a finite family `M` of pairwise-commuting observables (`∀ i j, (M i).Commutes (M j)`) measured
on a state `ρ`, there exist a finite outcome space `Ω`, a single joint measurement `m`, real value
functions `X j` (the result of `M j`), and pointer states `ψ` such that

* `m.bornProb ρ` is a genuine classical probability distribution (non-negative, total mass one);
* every outcome `ω` is a simultaneous eigenstate `ψ ω` of each `M j` with definite value `X j ω`;
* each observable's quantum expectation is the classical average of `X j` over the joint
  distribution, `∑ ω, m.bornProb ρ ω * X j ω = ρ.expectation (M j)`.

Hence the outcome random variables `X j` live on one classical sample space `(Ω, m.bornProb ρ)` and
reproduce the quantum statistics — they obey classical probability arguments. -/
theorem commuting_observables_classicalProbability {S : QSystem} {ι : Type*} [Finite ι]
    (M : ι → Observable S) (ρ : State S) (hM : ∀ i j, (M i).Commutes (M j)) :
    ∃ (Ω : Type) (_ : Fintype Ω) (m : Measurement Ω S) (X : ι → Ω → ℝ) (ψ : Ω → PureState S),
      (∀ ω, 0 ≤ m.bornProb ρ ω) ∧ (∑ ω, m.bornProb ρ ω = 1) ∧
      (∀ j ω, (M j).HasEigenstate (X j ω) (ψ ω)) ∧
      (∀ j, ∑ ω, m.bornProb ρ ω * X j ω = ρ.expectation (M j)) := sorry

end AxQM
