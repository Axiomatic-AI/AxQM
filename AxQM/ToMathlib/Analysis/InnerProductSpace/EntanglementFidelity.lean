/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-! # The entanglement fidelity of a quantum operation and its concentration in one element

For a finite family of operation elements `E : ι → (H →L[ℂ] H)` — the Kraus operators of a
trace-preserving quantum operation `E(ρ) = Σᵢ Eᵢ ρ Eᵢ†` — the **entanglement fidelity** of a state
`ρ` is the real number
`F(ρ, E) = Σᵢ |tr(ρ Eᵢ)|²`
(Nielsen–Chuang, *Quantum Computation and Quantum Information*, Eq. (9.135)). This is the
computational formula for the intrinsic entanglement fidelity `F(ρ, E) = ⟨RQ|(I ⊗ E)(|RQ⟩⟨RQ|)|RQ⟩`
(Eqs. (9.128)–(9.135)) obtained from any operator-sum representation of the operation.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §9.3 (Eqs. (9.135), (9.146); Problem 9.2).
-/

open scoped InnerProductSpace ComplexConjugate

@[expose] public section

namespace ContinuousLinearMap

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

/-- The **entanglement fidelity** `F(ρ, E) = Σᵢ |tr(ρ Eᵢ)|²` of a state `ρ` under the
trace-preserving quantum operation with operation elements `E : ι → (H →L[ℂ] H)`, i.e. `E(ρ) =
Σᵢ Eᵢ ρ Eᵢ†` (Nielsen & Chuang, Eq. (9.135)). -/
noncomputable def entanglementFidelity (ρ : H →L[ℂ] H) (E : ι → H →L[ℂ] H) : ℝ :=
  ∑ i, ‖LinearMap.trace ℂ H ((ρ * E i : H →L[ℂ] H) : H →ₗ[ℂ] H)‖ ^ 2

omit [FiniteDimensional ℂ H] in
/-- **Nielsen & Chuang, Problem 9.2.** For every state `ρ` and every trace-preserving quantum
operation — presented by operation elements `E : Fin n → (H →L[ℂ] H)` — there is a set of operation
elements `F` *for the same operation* (`krausSumₗ F = krausSumₗ E`) in which all the entanglement
fidelity is carried by the first element: `tr(ρ Fᵢ) = 0` for every `i ≠ 0`, and
`F(ρ, E) = |tr(ρ F₀)|²`  (Eq. (9.146)).
-/
theorem exists_krausSumₗ_eq_entanglementFidelity_eq_normSq_trace
    {n : ℕ} [NeZero n] (ρ : H →L[ℂ] H) (E : Fin n → H →L[ℂ] H) :
    ∃ F : Fin n → H →L[ℂ] H, krausSumₗ F = krausSumₗ E ∧
      (∀ i, i ≠ 0 → LinearMap.trace ℂ H ((ρ * F i : H →L[ℂ] H) : H →ₗ[ℂ] H) = 0) ∧
      entanglementFidelity ρ E
        = ‖LinearMap.trace ℂ H ((ρ * F 0 : H →L[ℂ] H) : H →ₗ[ℂ] H)‖ ^ 2 := sorry

end ContinuousLinearMap
