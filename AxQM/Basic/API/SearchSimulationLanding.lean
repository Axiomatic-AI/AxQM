/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SearchSimulationStep
import AxQM.Basic.API.Evolution
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumChoi

/-!
# AxQM.Basic.API — the search-simulation step as an `Evolution`, and its exact landing

The physics behind **Nielsen & Chuang, Exercise 6.10**: the lowest-order quantum-search
simulation step.

## Main declarations
* `searchStepEvolution θ Δt` — the step `U(Δt)` as a genuine `Evolution qubit`: the sequential
  composition (`Evolution.comp`) of the two projector-Hamiltonian propagators of Exercise 6.7
  (`projObservable.propagator`), the `|ψ⟩`-propagator applied second. It is a unitary evolution
  because each factor is (`Observable.propagator`).
-/

open scoped InnerProductSpace
open Matrix Complex ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The search-simulation step `U(Δt)` as an `Evolution`** (Nielsen & Chuang, Exercise 6.9/6.10).
`U(Δt) = exp(−i|ψ⟩⟨ψ|Δt) exp(−i|x⟩⟨x|Δt)` for the effective search qubit, with `|x⟩ = |0⟩ =
blochPureState 0 0` and `|ψ⟩ = blochPureState θ 0`: the sequential composition (`Evolution.comp`) of
the two Exercise 6.7 projector-Hamiltonian propagators (`projObservable.propagator`), the
`|ψ⟩`-propagator applied second. A genuine unitary `Evolution` of the qubit. -/
def searchStepEvolution (θ Δt : ℝ) : Evolution qubit :=
  ((blochPureState θ 0).projObservable.propagator 1 0 Δt).comp
    ((blochPureState 0 0).projObservable.propagator 1 0 Δt)

end AxQM
