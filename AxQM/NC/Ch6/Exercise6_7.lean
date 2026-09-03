/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.MarkingOracle
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ProjectorHamiltonian
import AxQM.Basic.API.Evolution

/-!
# Nielsen & Chuang, Exercise 6.7 (circuits simulating `exp(-i|x⟩⟨x|Δt)` and `exp(-i|ψ⟩⟨ψ|Δt)`)

*(N&C p. 258.)*

Verify circuits in Figs 6.4/6.5 implement exp(-i|x><x|dt) and exp(-i|psi><psi|dt).

* `hamSimCircuit_evolvePure_tmul_zero` — N&C Exercise 6.7, Figure 6.4: for an arbitrary marked pure
  state `x` (generalising N&C's computational-basis marked item), the compute–phase–uncompute
  circuit `hamSimCircuit x Δt` (two calls to the marking oracle around the phase gate `P(-Δt)`)
  implements `exp(-i|x⟩⟨x|Δt)`: `hamSimCircuit x Δt |>.evolvePure (φ ⊗ |0⟩) = (exp(-i|x⟩⟨x|Δt) φ) ⊗
  |0⟩` for every query state `φ`.
* `hamSimCircuitConj` — N&C Exercise 6.7, Figure 6.5 (the circuit): the Figure 6.4 circuit for a
  reference marked state `x`, conjugated on the query register by a state-preparation unitary `W`,
  `hamSimCircuitConj W x Δt = (W ⊗ I) · hamSimCircuit x Δt · (W† ⊗ I)` — the "`H^{⊗n}`, marked-state
  circuit, `H^{⊗n}`" sandwich of Figure 6.5.
* `hamSimCircuitConj_evolvePure_tmul_zero` — N&C Exercise 6.7, Figure 6.5: that circuit implements
  `exp(-i|ψ⟩⟨ψ|Δt)` for the transported state `|ψ⟩ = W|x⟩` (`W.evolvePure x`): with the response
  qubit in `|0⟩`, `hamSimCircuitConj W x Δt |>.evolvePure (φ ⊗ |0⟩) = (exp(-i|ψ⟩⟨ψ|Δt) φ) ⊗ |0⟩` for
  every query state `φ`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 6.7 — Figure 6.4 implements `exp(-i|x⟩⟨x|Δt)`.** For an arbitrary
marked pure state `x` (generalising N&C's computational-basis marked item), the
compute–phase–uncompute circuit `hamSimCircuit x Δt` — the marking oracle, then the
response-qubit phase gate `P(-Δt) = diag(1, e^{-iΔt})`, then the marking oracle again (N&C's
**two oracle calls**) — implements the projector-Hamiltonian propagator `exp(-i|x⟩⟨x|Δt)`: with
the response qubit supplied in `|0⟩`, for **every** query state `φ`, `hamSimCircuit x Δt
|>.evolvePure (φ ⊗ |0⟩) = (exp(-i|x⟩⟨x|Δt) φ) ⊗ |0⟩`, where the target is the genuine propagator
`x.projObservable.propagator 1 0 Δt` of the `|x⟩⟨x|` Hamiltonian and the response is returned to
`|0⟩`. -/
theorem hamSimCircuit_evolvePure_tmul_zero (x : PureState S) (Δt : ℝ) (φ : PureState S) :
    (hamSimCircuit x Δt).evolvePure (φ.tmul (qubitBasis 0))
      = ((x.projObservable.propagator 1 0 Δt).evolvePure φ).tmul (qubitBasis 0) := sorry

/-- **The Figure 6.5 circuit** for `exp(-i|ψ⟩⟨ψ|Δt)`. The Figure 6.4 marked-state circuit
`hamSimCircuit x Δt` (for a reference marked state `x`), conjugated on the query register by a
state-preparation unitary `W`. This is N&C's Figure 6.5 — the "`H^{⊗n}`, marked-state circuit,
`H^{⊗n}`" sandwich — for the general state-preparation unitary `W`; N&C's figure is the case `W
= H^{⊗n}`, `x = |0⟩`, carrying the marked reference `|0⟩` to the uniform superposition `|ψ⟩ =
H^{⊗n}|0⟩` (eq. 6.24). -/
def hamSimCircuitConj (W : Evolution S) (x : PureState S) (Δt : ℝ) : Evolution (S ⊗ qubit) :=
  (W.onLeft qubit).comp ((hamSimCircuit x Δt).comp (W.adjoint.onLeft qubit))

/-- **Nielsen & Chuang, Exercise 6.7 — Figure 6.5 implements `exp(-i|ψ⟩⟨ψ|Δt)`.** For a
state-preparation unitary `W` and a reference marked state `x`, the conjugated circuit
`hamSimCircuitConj W x Δt` implements the projector-Hamiltonian propagator of the *transported*
state `|ψ⟩ = W|x⟩` (`W.evolvePure x`): with the response qubit supplied in `|0⟩`, for **every**
query state `φ`, `hamSimCircuitConj W x Δt |>.evolvePure (φ ⊗ |0⟩) = (exp(-i|ψ⟩⟨ψ|Δt) φ) ⊗ |0⟩`,
where the target is the genuine propagator `(W.evolvePure x).projObservable.propagator 1 0 Δt`
and the response is returned to `|0⟩`. **N&C's exercise** ("`|ψ⟩` as in (6.24)") is the special
case `W = H^{⊗n}`, `x = |0⟩`, so `|ψ⟩ = H^{⊗n}|0⟩` is the uniform superposition (6.24); the
general `(W, x)` statement subsumes it. -/
theorem hamSimCircuitConj_evolvePure_tmul_zero (W : Evolution S) (x : PureState S) (Δt : ℝ)
    (φ : PureState S) :
    (hamSimCircuitConj W x Δt).evolvePure (φ.tmul (qubitBasis 0))
      = (((W.evolvePure x).projObservable.propagator 1 0 Δt).evolvePure φ).tmul (qubitBasis 0) :=
        sorry

end AxQM
