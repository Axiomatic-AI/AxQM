/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch8.Problem8_3
import AxQM.NC.Ch2.Exercise2_72
import AxQM.Basic.API.Fidelity
import AxQM.Basic.API.TraceDistance
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
import AxQM.Concrete.ClassicalTraceDistance
import AxQM.Basic.API.HSOverlap
import AxQM.Basic.API.BlochState
import AxQM.Concrete.BlochMatrix
import AxQM.Basic.API.Qubit

/-!
# Nielsen & Chuang, Exercise 10.12 (Fidelity for the depolarizing channel; minimum fidelity)

*(N&C p. 441.)*

Fidelity between |0> and E(|0><0|) for depolarizing channel is sqrt(1-2p/3); min fidelity argument.

* `depolarizingProb_nonneg`
* `depolarizingProb_sum`
* `pauliDepolarizingChannel`
* `pauliDepolarizingChannel_fidelity_ket0`
* `pauliDepolarizingChannel_isLeast_fidelity`
-/

open Matrix

noncomputable section

namespace AxQM

/-- The depolarizing weights `![1 − p, p/3, p/3, p/3]` over `I, X, Y, Z` are **nonnegative**, for
`0 ≤ p ≤ 1`: `1 − p ≥ 0` and `p/3 ≥ 0`. -/
theorem depolarizingProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ i, 0 ≤ (![1 - p, p / 3, p / 3, p / 3] : Fin 4 → ℝ) i := by
  intro i
  fin_cases i <;> simp <;> linarith

/-- The depolarizing weights `![1 − p, p/3, p/3, p/3]` **sum to one**:
`(1 − p) + p/3 + p/3 + p/3 = 1`. -/
theorem depolarizingProb_sum (p : ℝ) :
    ∑ i, (![1 - p, p / 3, p / 3, p / 3] : Fin 4 → ℝ) i = 1 := by
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]
  ring

/-- **The single-qubit depolarizing channel** `E(ρ) = (1 − p)ρ + (p/3)(XρX + YρY + ZρZ)` (Nielsen &
Chuang §10.3.2, eq. 10.42), for depolarizing probability `0 ≤ p ≤ 1`. Realised as the qubit
Pauli channel (`AxQM.pauliChannel`, Problem 8.3) with the weight distribution `![1 − p,
p/3, p/3, p/3]` over the Paulis `I, X, Y, Z`: identity with probability `1 − p`, and each of `X,
Y, Z` with probability `p/3`. -/
def pauliDepolarizingChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : State qubit → State qubit :=
  (pauliChannel ![1 - p, p / 3, p / 3, p / 3] (depolarizingProb_nonneg hp0 hp1)
    (depolarizingProb_sum p)).apply

/-- **Nielsen & Chuang, Exercise 10.12 (the `|0⟩` case).** The fidelity between `|0⟩` and
`E(|0⟩⟨0|)` for the depolarizing channel is `√(1 − 2p/3)`. -/
theorem pauliDepolarizingChannel_fidelity_ket0 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (qubitBasis 0).toState.fidelity (pauliDepolarizingChannel p hp0 hp1 (qubitBasis 0).toState)
      = Real.sqrt (1 - 2 * p / 3) := sorry

/-- **Nielsen & Chuang, Exercise 10.12 (the minimum fidelity).** `√(1 − 2p/3)` is the *minimum*
fidelity of the depolarizing channel over pure input states: it is `IsLeast` of the set of
per-state fidelities `{F | ∃ ψ, F(|ψ⟩, E(|ψ⟩⟨ψ|)) = F}`. -/
theorem pauliDepolarizingChannel_isLeast_fidelity (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsLeast {F : ℝ | ∃ ψ : PureState qubit,
        ψ.toState.fidelity (pauliDepolarizingChannel p hp0 hp1 ψ.toState) = F}
      (Real.sqrt (1 - 2 * p / 3)) := sorry

end AxQM
