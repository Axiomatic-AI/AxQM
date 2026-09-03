/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliExpansion
import AxQM.Basic.API.Evolution
import AxQM.ToMathlib.Analysis.Normed.Algebra.LieTrotter
import AxQM.Basic.API.HamiltonianGenerator
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# AxQM.Basic.API — the literal Pauli-string Trotter approximation (N&C Problem 4.3)

Nielsen & Chuang, Problem 4.3, in the *literal* form in which the approximating product runs over
the `4ⁿ` Pauli strings.

## Main declarations
* `pauliStringHamiltonian g c` — the **Pauli-string Hamiltonian** `c · g` on `qudit (2ⁿ)`: the
  real-scaled Pauli string `Concrete.pauliStringStd g` promoted to a self-adjoint operator through
  `Matrix.toEuclideanCLM`. Its propagator `(pauliStringHamiltonian g (h g)).propagator 1 0 Δ` is
  exactly N&C's `exp(-i h_g g Δ)`.
* `Observable.exists_norm_prod_pauliStringHamiltonian_propagator_sub_le` — **part (4)**, literal
  form: `‖(∏_g exp(-i h_g g Δ)) - exp(-i H Δ)‖ ≤ C·Δ²`.
-/

open scoped InnerProductSpace

open Matrix

noncomputable section

namespace AxQM

variable {d n : ℕ}

/-- The **Pauli-string Hamiltonian** `c · g` on the `n`-qubit register `qudit (2ⁿ)`, for a Pauli
string `g : Fin n → Fin 4` and a real coefficient `c`. These are the summands `h_g · g` of the
Pauli expansion of a Hamiltonian, whose ordered propagator product is Trotterised in Nielsen &
Chuang, Problem 4.3(4)/(5). -/
def pauliStringHamiltonian (g : Fin n → Fin 4) (c : ℝ) : Observable (qudit (2 ^ n)) where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)) ((c : ℂ) • Concrete.pauliStringStd g)
  selfAdjoint := by
    have hc : IsSelfAdjoint (c : ℂ) := (Complex.im_eq_zero_iff_isSelfAdjoint ↑c).mp rfl
    exact (hc.smul (Concrete.pauliStringStd_isHermitian g).isSelfAdjoint).map
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)))

/-- **Nielsen & Chuang, Problem 4.3(4): first-order Trotter error, literal Pauli-string form.** For
a Hamiltonian `H` on the `n`-qubit register, splitting its propagator `exp(-i H Δ)` into ordered
product `∏_g exp(-i h_g g Δ)` over the `4ⁿ` Pauli-string propagators incurs only a second-order
error: there are real coefficients `h_g` and a constant `C ≥ 0` with `‖(∏_g exp(-i h_g g Δ)) -
exp(-i H Δ)‖ ≤ C·Δ²` for every `Δ ∈ [0, 1]`. -/
theorem Observable.exists_norm_prod_pauliStringHamiltonian_propagator_sub_le
    (H : Observable (qudit (2 ^ n))) :
    ∃ (h : (Fin n → Fin 4) → ℝ) (C : ℝ), 0 ≤ C ∧ ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ 1 →
      ‖(Finset.univ.toList.map fun g =>
            ((pauliStringHamiltonian g (h g)).propagator 1 0 Δ).op).prod
          - (H.propagator 1 0 Δ).op‖ ≤ C * Δ ^ 2 := sorry

end AxQM
