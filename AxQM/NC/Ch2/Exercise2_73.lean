/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.MinimalEnsembleProbability

/-!
# Nielsen & Chuang, Exercise 2.73 (minimal ensemble through a support vector)

*(N&C p. 105.)*

Minimal ensemble for rho containing |psi> in support, with p_i=1/<psi|rho^-1|psi>.

* `exists_isMinimalFor_states_eq_of_memSupport` — existence: for `|ψ⟩` in the support of `ρ`
  (`PureState.MemSupport`), some minimal ensemble for `ρ` (`Ensemble.IsMinimalFor`, size `rank ρ`)
  has `|ψ⟩` as one of its states.
* `prob_eq_inv_pseudoInverseExpectation` — probability formula: in any minimal ensemble for `ρ`,
  each state `|ψᵢ⟩` appears with weight `pᵢ = 1/⟨ψᵢ|ρ⁻¹|ψᵢ⟩`, where `⟨ψᵢ|ρ⁻¹|ψᵢ⟩` is the
  pseudo-inverse expectation `State.pseudoInverseExpectation`.
-/

namespace AxQM

variable {S : QSystem}

/-- **Nielsen–Chuang Exercise 2.73 (existence).** For a pure state `|ψ⟩` in the support of `ρ`
(`ψ.MemSupport ρ`) there is a *minimal* ensemble for `ρ` (`Ensemble.IsMinimalFor`, of size `rank
ρ`) that **contains** `|ψ⟩`: one of its pure states equals `|ψ⟩`.
-/
theorem exists_isMinimalFor_states_eq_of_memSupport (ρ : State S) (ψ : PureState S)
    (h : ψ.MemSupport ρ) :
    ∃ e : Ensemble S, e.IsMinimalFor ρ ∧ ∃ i, e.states i = ψ := sorry

/-- **Nielsen–Chuang Exercise 2.73 (probability formula).** In any minimal ensemble `{pᵢ, |ψᵢ⟩}` for
`ρ`, each state `|ψᵢ⟩` appears with probability
`pᵢ = 1 / ⟨ψᵢ|ρ⁻¹|ψᵢ⟩`,
where `⟨ψᵢ|ρ⁻¹|ψᵢ⟩` is the pseudo-inverse expectation `State.pseudoInverseExpectation` (the matrix
element of the "inverse on the support" `ρ⁻¹` in `|ψᵢ⟩`). N&C eq. (2.176). -/
theorem Ensemble.IsMinimalFor.prob_eq_inv_pseudoInverseExpectation {e : Ensemble S} {ρ : State S}
    (hmin : e.IsMinimalFor ρ) (i : Fin e.card) :
    e.prob i = 1 / ρ.pseudoInverseExpectation (e.states i) := sorry

end AxQM
