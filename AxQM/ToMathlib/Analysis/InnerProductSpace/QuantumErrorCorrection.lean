/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumComposition
public import Mathlib.RingTheory.Idempotents

/-! # The Knill–Laflamme quantum error-correction conditions

This file develops the **Knill–Laflamme quantum error-correction conditions** (Nielsen & Chuang,
*Quantum Computation and Quantum Information*, **Theorem 10.1**) as general operator theory on a
complex inner product space `H`, alongside the operator-sum (Kraus) representation
(`ContinuousLinearMap.krausSumₗ`).

## Main definitions

* `ContinuousLinearMap.SatisfiesKLConditions P E α` — the Knill–Laflamme conditions
  `P Eᵢ† Eⱼ P = αᵢⱼ P` for the code projector `P`, operation elements `E`, and coefficient matrix
  `α` (N&C eq. (10.16)).
-/

@[expose] public section

open scoped InnerProductSpace Matrix
open Finset

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

/-- **The Knill–Laflamme quantum error-correction conditions** (Nielsen & Chuang, Theorem 10.1,
eq. (10.16)). For a code projector `P : H →L[ℂ] H` and a finite family of operation elements
`E : ι → H →L[ℂ] H`, the family satisfies the conditions with coefficient matrix `α` when
`P Eᵢ† Eⱼ P = αᵢⱼ P` for all `i, j`, where `Eᵢ† = adjoint (E i)`. N&C additionally require `α` to be
Hermitian; that hypothesis is supplied where it is used. -/
def SatisfiesKLConditions (P : H →L[ℂ] H) (E : ι → H →L[ℂ] H) (α : Matrix ι ι ℂ) : Prop :=
  ∀ i j, P ∘L adjoint (E i) ∘L E j ∘L P = α i j • P

variable {P : H →L[ℂ] H} {E F : ι → H →L[ℂ] H} {α : Matrix ι ι ℂ} {d : ι → ℝ}

/-- **A recovery operation `R` corrects the errors `E` on the code with projector `P`** (Nielsen &
Chuang, Theorem 10.1, eq. (10.15)). The combined noise-then-recovery operation `ρ ↦ (R ∘ E)(ρ) =
krausSumₗ R (krausSumₗ E ρ)` returns every operator `ρ` supported on the code (`P ρ P = ρ`) to a
scalar multiple of itself. -/
def Corrects (P : H →L[ℂ] H) (E : ι → H →L[ℂ] H) {κ : Type*} [Fintype κ]
    (R : κ → H →L[ℂ] H) : Prop :=
  ∀ ρ : H →L[ℂ] H, P ∘L ρ ∘L P = ρ → ∃ c : ℂ, krausSumₗ R (krausSumₗ E ρ) = c • ρ

universe u

/-- **The Knill–Laflamme quantum error-correction conditions** (Nielsen & Chuang, Theorem 10.1) —
the biconditional. For a nonzero orthogonal code projector `P` and a finite family of operation
elements `E` (the noise) on a finite-dimensional complex inner product space, there exists a
**trace-preserving** recovery operation `R` (`∑ₒ Rₒ† Rₒ = 1`) that **corrects** `E` on the code
(`Corrects P E R`) **iff** the errors satisfy `P Eᵢ† Eⱼ P = αᵢⱼ P` for a **Hermitian** matrix
`α`. -/
theorem satisfiesKLConditions_iff_exists_correction {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H] {ι : Type u} [Fintype ι]
    {P : H →L[ℂ] H} {E : ι → H →L[ℂ] H}
    (hP : IsSelfAdjoint P) (hPidem : P ∘L P = P) (hP0 : P ≠ 0) :
    (∃ (κ : Type u) (_ : Fintype κ) (R : κ → H →L[ℂ] H),
        (∑ o, adjoint (R o) ∘L R o = 1) ∧ Corrects P E R) ↔
      ∃ α : Matrix ι ι ℂ, α.IsHermitian ∧ SatisfiesKLConditions P E α := sorry

end ContinuousLinearMap
