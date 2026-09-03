/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumTheorem
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumComposition

/-!
# AxQM.Basic.API — quantum channels (CPTP maps on states)

A **quantum channel** is the completely-positive trace-preserving (CPTP) evolution of an open
quantum system: the trace-preserving special case of a Nielsen & Chuang *quantum operation*
(Chapter 8). Abstractly it is a linear superoperator `Φ` on operators that is completely positive
(N&C axiom A3) and trace-preserving (`tr Φ(A) = tr A`, N&C's trace condition with *equality* — a
deterministic process, no measurement outcome discarded). By the operator-sum representation
theorem such a `Φ` is exactly one of the form `ρ ↦ ∑ₖ Eₖ ρ Eₖ†` with the
**completeness relation** `∑ₖ Eₖ† Eₖ = I`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A quantum channel (CPTP map) on the states of `S`.** A state-map `f : State S → State S` is a
**channel** when it is the restriction to states of a linear superoperator `Φ` on the operators of
`S.space` that is

* **completely positive** (`ContinuousLinearMap.IsCompletelyPositive`, Nielsen & Chuang axiom A3),
  and
* **trace-preserving**, `tr Φ(A) = tr A` for every operator `A` (N&C's trace condition with
  equality — the process is deterministic).

i.e. `(f ρ).op = Φ ρ.op` for every state `ρ`. This is Nielsen & Chuang's *trace-preserving quantum
operation*; by the operator-sum representation theorem it is equivalently a map
`ρ ↦ ∑ₖ Eₖ ρ Eₖ†` with `∑ₖ Eₖ† Eₖ = I`. It is the object over which
**Problem 8.3**'s "unital channel" ranges. -/
def IsChannel (f : State S → State S) : Prop :=
  ∃ Φ : (S.space →L[ℂ] S.space) →ₗ[ℂ] (S.space →L[ℂ] S.space),
    ContinuousLinearMap.IsCompletelyPositive Φ ∧
    (∀ A : S.space →L[ℂ] S.space,
      LinearMap.trace ℂ S.space ↑(Φ A) = LinearMap.trace ℂ S.space ↑A) ∧
    ∀ ρ : State S, (f ρ).op = Φ ρ.op

end AxQM
