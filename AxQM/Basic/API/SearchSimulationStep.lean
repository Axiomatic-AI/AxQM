/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ProjectorHamiltonian
import AxQM.Basic.API.BlochState
import AxQM.Concrete.SearchSimulationStep

/-!
# AxQM.Basic.API — the search-simulation step `U(Δt)` (Nielsen & Chuang, Eq. 6.25)

The physics of **Nielsen & Chuang, Exercise 6.9**: the explicit form of the lowest-order
quantum-search simulation step `U(Δt)`.

## Main declarations
* `searchSimulationStep_op` — **Exercise 6.9, Eq. 6.25 at the operator level.** The composite `U(Δt)
  = exp(−i|ψ⟩⟨ψ|Δt) ∘ exp(−i|x⟩⟨x|Δt)` (operator product, `ψ`-propagator applied second) equals the
  global phase `e^{−iΔt}` times `Matrix.toEuclideanCLM (Concrete.searchStepReduced Δt ⃗ψ ẑ)`, the
  N&C eq.-6.25 reduced form `(c² − s² ⃗ψ·ẑ) I − 2is (c (⃗ψ+ẑ)/2 + s (⃗ψ×ẑ)/2)·σ` (`c = cos(Δt/2)`,
  `s = sin(Δt/2)`).
-/

open scoped InnerProductSpace
open Matrix Complex ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 6.9 — verification of Eq. 6.25 (operator level).** The lowest-order
quantum-search simulation step `U(Δt) = exp(−i|ψ⟩⟨ψ|Δt) exp(−i|x⟩⟨x|Δt)` — the operator product
of the two projector-Hamiltonian propagators, the `|ψ⟩`-factor applied second — for `|x⟩ = |0⟩ =
blochPureState 0 0` (Bloch vector `ẑ`) and `|ψ⟩ = cos(θ/2)|0⟩ + sin(θ/2)|1⟩ = blochPureState θ
0` (Bloch vector `⃗ψ = (sin θ, 0, cos θ)`) equals

`U(Δt) = e^{−iΔt} · [(c² − s² ⃗ψ·ẑ) I − 2is (c (⃗ψ+ẑ)/2 + s (⃗ψ×ẑ)/2)·σ]`

(`c = cos(Δt/2)`, `s = sin(Δt/2)`), i.e. `e^{−iΔt}` times `Matrix.toEuclideanCLM
(Concrete.searchStepReduced Δt ⃗ψ ẑ)`. The unimportant global phase `e^{−iΔt}` of N&C's "up to a
global phase factor" is here made explicit.
-/
theorem searchSimulationStep_op (θ Δt : ℝ) :
    ((blochPureState θ 0).projObservable.propagator 1 0 Δt).op
        * ((blochPureState 0 0).projObservable.propagator 1 0 Δt).op
      = Complex.exp (-(Complex.I * (Δt : ℂ)))
          • Matrix.toEuclideanCLM (𝕜 := ℂ)
              (Concrete.searchStepReduced Δt (Concrete.blochSphereVector θ 0)
                (Concrete.blochSphereVector 0 0)) := sorry

end AxQM
