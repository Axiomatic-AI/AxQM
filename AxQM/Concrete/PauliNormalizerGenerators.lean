/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliNormalizer
import AxQM.Concrete.PauliStringEncodingPhaseCZLayer

/-!
# Concrete: a unitary is fixed up to a global phase by its conjugation of the generators

Nielsen & Chuang, Exercise 10.38: a unitary on two qubits is determined, up to a global phase, by
how it conjugates the four single-qubit generators `X₁, X₂, Z₁, Z₂`.
-/

open Matrix

noncomputable section

namespace AxQM.Concrete

variable {n : ℕ}

/-- **Nielsen & Chuang, Exercise 10.38.** Two unitaries `U, V` on two qubits that conjugate the four
generators `X₁ = X ⊗ I`, `X₂ = I ⊗ X`, `Z₁ = Z ⊗ I`, `Z₂ = I ⊗ Z` — i.e. `pauliString (xGenPauli
i)` and `pauliString (zGenPauli i)` for `i ∈ {0, 1}` — in the same way agree up to a global
phase: `U = c • V` for a unit scalar `c` (`‖c‖ = 1`). -/
theorem unitary_eq_smul_of_conj_twoQubitGenerators
    {U V : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2 → Fin 2) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin 2 → Fin 2) ℂ)
    (hX₁ : U * pauliString (xGenPauli 0) * Uᴴ = V * pauliString (xGenPauli 0) * Vᴴ)
    (hX₂ : U * pauliString (xGenPauli 1) * Uᴴ = V * pauliString (xGenPauli 1) * Vᴴ)
    (hZ₁ : U * pauliString (zGenPauli 0) * Uᴴ = V * pauliString (zGenPauli 0) * Vᴴ)
    (hZ₂ : U * pauliString (zGenPauli 1) * Uᴴ = V * pauliString (zGenPauli 1) * Vᴴ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ U = c • V := sorry

/-- **The global phase in Exercise 10.38 is necessary.** N&C's literal "`U = V`" fails: there are
two *distinct* two-qubit unitaries that conjugate every generator identically. -/
theorem exists_ne_unitary_conj_twoQubitGenerators_eq :
    ∃ U V : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ,
      U ∈ Matrix.unitaryGroup (Fin 2 → Fin 2) ℂ ∧
      V ∈ Matrix.unitaryGroup (Fin 2 → Fin 2) ℂ ∧
      U * pauliString (xGenPauli 0) * Uᴴ = V * pauliString (xGenPauli 0) * Vᴴ ∧
      U * pauliString (xGenPauli 1) * Uᴴ = V * pauliString (xGenPauli 1) * Vᴴ ∧
      U * pauliString (zGenPauli 0) * Uᴴ = V * pauliString (zGenPauli 0) * Vᴴ ∧
      U * pauliString (zGenPauli 1) * Uᴴ = V * pauliString (zGenPauli 1) * Vᴴ ∧
      U ≠ V := sorry

end AxQM.Concrete

end
