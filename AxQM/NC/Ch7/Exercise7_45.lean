/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliTrotter
import AxQM.Concrete.PauliString
import AxQM.ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM
import AxQM.Concrete.NmrTomographyExperimentCount

/-!
# Nielsen & Chuang, Exercise 7.45 (State tomography with NMR)

*(N&C p. 336.)*

State tomography with NMR: show nine experiments (given M_k rotations) suffice to reconstruct
two-spin ρ.

* `twoSpin_state_eq_of_expectation_nineExperiments` —
  `twoSpin_state_eq_of_expectation_nineExperiments` (below) — the nine-experiment claim: two states
  of `qudit (2²)` that agree on `⟨P_g⟩` for every Pauli string `g` observed by some of the nine
  experiments are equal.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 7.45 — nine experiments suffice.** Two states `ρ`, `σ` of the
two-qubit register `qudit (2²)` that agree on the expectation `⟨P_g⟩` of every two-qubit
Pauli-string observable `P_g = pauliStringHamiltonian g 1` **observed by some one of the nine
experiments** are equal: `ρ = σ`.
-/
theorem twoSpin_state_eq_of_expectation_nineExperiments {ρ σ : State (qudit (2 ^ 2))}
    (h : ∀ g : Fin 2 → Fin 4,
        (∃ s ∈ (Finset.univ : Finset (Fin 2 → Fin 3)), Concrete.SettingObserves s g) →
          ρ.expectation (pauliStringHamiltonian g 1)
            = σ.expectation (pauliStringHamiltonian g 1)) :
    ρ = σ := sorry

end AxQM
