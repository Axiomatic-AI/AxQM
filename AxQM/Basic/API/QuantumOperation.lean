/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumTheorem

/-!
# AxQM.Basic.API — quantum operations (the operator-sum representation theorem)

A **quantum operation** is the general (not necessarily deterministic) evolution of an open quantum
system — Nielsen & Chuang's object of Chapter 8, of which a *quantum channel* (CPTP) is the
trace-preserving special case. Abstractly it is a linear
superoperator `Φ` on operators that is **completely positive** (N&C axiom A3) and
**trace-non-increasing** (`re tr Φ(A) ≤ re tr A` for positive `A`; N&C axiom A1, so that
`tr[Φ(ρ)] ≤ 1` is a probability). By the operator-sum representation theorem (N&C **Theorem 8.1**)
such a `Φ` is exactly one of the form `ρ ↦ ∑ₖ Eₖ ρ Eₖ†` with the **trace condition**
`∑ₖ Eₖ† Eₖ ≤ I` — the inequality (not the equality of a channel), since a general operation may
occur with probability `< 1`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **A quantum operation from system `S` to system `T`** (Nielsen & Chuang, Chapter 8; the object
of the operator-sum representation theorem, **Theorem 8.1**). A superoperator
`Φ : (S.space →L[ℂ] S.space) →ₗ[ℂ] (T.space →L[ℂ] T.space)` is a quantum operation when it is

* **completely positive** (`ContinuousLinearMap.IsCompletelyPositive`, N&C axiom A3), and
* **trace-non-increasing** (`ContinuousLinearMap.IsTraceNonIncreasing`, N&C axiom A1: for every
  positive operator `A`, `re tr(Φ A) ≤ re tr A`, so that `tr[Φ(ρ)] ≤ 1` on a state `ρ`).

Axiom A2 (convex-linearity on density operators) is subsumed by the `ℂ`-linearity of `Φ`. N&C
allows the input system `S` and output system `T` to differ; the same-system case is `T = S`. -/
def IsQuantumOperation (Φ : (S.space →L[ℂ] S.space) →ₗ[ℂ] (T.space →L[ℂ] T.space)) : Prop :=
  ContinuousLinearMap.SatisfiesOperationAxioms Φ

/-- **Nielsen–Chuang Theorem 8.1, for a quantum system.** A superoperator `Φ` between the operators
of quantum systems `S` and `T` is a quantum operation (`IsQuantumOperation`, i.e. completely
positive and trace-non-increasing — axioms A1, A2, A3) **iff** it admits an operator-sum (Kraus)
representation: a finite family of operation elements `E : ι → (S.space →L[ℂ] T.space)` with
`Φ ρ = ∑ₖ Eₖ ρ Eₖ†` (`Φ = krausSumₗ E`) and the trace condition `∑ₖ Eₖ† Eₖ ≤ 1`
(`ContinuousLinearMap.IsOperatorSum E Φ`). -/
theorem isQuantumOperation_iff_isOperatorSum
    (Φ : (S.space →L[ℂ] S.space) →ₗ[ℂ] (T.space →L[ℂ] T.space)) :
    IsQuantumOperation Φ ↔
      ∃ (ι : Type) (_ : Fintype ι) (E : ι → S.space →L[ℂ] T.space),
        ContinuousLinearMap.IsOperatorSum E Φ := sorry

end AxQM
