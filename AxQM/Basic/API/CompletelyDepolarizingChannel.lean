/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.MaximallyMixed
import AxQM.Basic.API.QuantumChannel
import AxQM.Concrete.PauliAverage

/-!
# AxQM.Basic.API — completely depolarizing qubit channel (Pauli operation elements)

The **completely depolarizing channel** on a single qubit is the noise process that discards all
information: whatever the input state `ρ`, the output is the completely randomized (maximally
mixed) state `I/2`. This file constructs its **operation elements (Kraus operators)** — the object
Nielsen & Chuang, Exercise 10.11 asks for — and the channel they define.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The four Pauli operators of the qubit** `σ₀ = I, σ₁ = X, σ₂ = Y, σ₃ = Z`, as a family
indexed by `Fin 4`. `σ₀` is the identity operator; `σ₁, σ₂, σ₃` are the operators of the Pauli
`X, Y, Z` observables. -/
def pauliFamilyOp : Fin 4 → qubit.space →L[ℂ] qubit.space
  | 0 => 1
  | 1 => pauliXObservable.op
  | 2 => pauliYObservable.op
  | 3 => pauliZObservable.op

/-- Each Pauli operator is **self-adjoint** (`σₖ† = σₖ`). -/
theorem pauliFamilyOp_selfAdjoint (k : Fin 4) : IsSelfAdjoint (pauliFamilyOp k) := by
  fin_cases k
  · exact IsSelfAdjoint.one _
  · exact pauliXObservable.selfAdjoint
  · exact pauliYObservable.selfAdjoint
  · exact pauliZObservable.selfAdjoint

/-- Each Pauli operator is an **involution** `σₖ² = I`. -/
theorem pauliFamilyOp_mul_self (k : Fin 4) : pauliFamilyOp k * pauliFamilyOp k = 1 := by
  fin_cases k
  · exact one_mul 1
  · exact pauliXObservable_op_mul_self
  · exact pauliYObservable_op_mul_self
  · exact pauliZObservable_op_mul_self

/-- **The operation elements of the completely depolarizing qubit channel** (Nielsen & Chuang,
Exercise 10.11): `Eₖ = ½ σₖ`, one half of each Pauli `σ₀ = I, σ₁ = X, σ₂ = Y, σ₃ = Z`. -/
def completelyDepolarizingKraus (k : Fin 4) : qubit.space →L[ℂ] qubit.space :=
  ((1 / 2 : ℝ) : ℂ) • pauliFamilyOp k

/-- Each operation element is **self-adjoint**: `Eₖ† = Eₖ`. -/
theorem completelyDepolarizingKraus_selfAdjoint (k : Fin 4) :
    adjoint (completelyDepolarizingKraus k) = completelyDepolarizingKraus k := by
  rw [completelyDepolarizingKraus, ← star_eq_adjoint, star_smul,
    isSelfAdjoint_iff.mp (pauliFamilyOp_selfAdjoint k), Complex.star_def, Complex.conj_ofReal]

/-- **The completeness relation** `∑ₖ Eₖ† Eₖ = I` for the completely depolarizing operation
elements (Nielsen & Chuang's trace condition, certifying `E` is trace preserving). -/
theorem completelyDepolarizingKraus_completeness :
    ∑ k, (adjoint (completelyDepolarizingKraus k)).comp (completelyDepolarizingKraus k) = 1 := by
  have hterm : ∀ k, (adjoint (completelyDepolarizingKraus k)).comp (completelyDepolarizingKraus k)
      = ((1 / 4 : ℝ) : ℂ) • 1 := by
    intro k
    rw [completelyDepolarizingKraus_selfAdjoint, completelyDepolarizingKraus, smul_comp, comp_smul,
      smul_smul, ← ContinuousLinearMap.mul_def, pauliFamilyOp_mul_self]
    rw [← Complex.ofReal_mul]
    norm_num
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

/-- **The completely depolarizing qubit channel** `E(ρ) = ∑ₖ Eₖ ρ Eₖ†` as a state map, the operator
sum of the Pauli operation elements `completelyDepolarizingKraus`. It is a genuine `State qubit
→ State qubit`. -/
def completelyDepolarizingChannel (ρ : State qubit) : State qubit where
  op := krausSumₗ completelyDepolarizingKraus ρ.op
  isDensity :=
    isDensityOp_krausSumₗ completelyDepolarizingKraus completelyDepolarizingKraus_completeness
      ρ.isDensity

end AxQM
