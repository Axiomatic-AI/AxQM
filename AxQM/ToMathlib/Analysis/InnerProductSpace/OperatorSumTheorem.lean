/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumChoi

/-!
# The operator-sum representation theorem (Nielsen–Chuang Theorem 8.1)

Nielsen & Chuang **Theorem 8.1** (*Quantum Computation and Quantum Information*, §8.2.4, Box 8.1,
Eq. (8.50)).

## Main results

* `ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum` — **N&C Theorem 8.1**: a
  superoperator `Φ` satisfies the operation axioms A1, A2, A3 iff it has an operator-sum (Kraus)
  representation.
-/

open scoped TensorProduct

noncomputable section

@[expose] public section

namespace ContinuousLinearMap

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]

/-- **Nielsen–Chuang Theorem 8.1 (operator-sum representation theorem).** A superoperator `Φ : (H
→L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)` satisfies the quantum-operation axioms A1, A2, A3
(`SatisfiesOperationAxioms`: completely positive and trace-non-increasing) **iff** it has an
operator-sum (Kraus) representation — a finite family of operation elements `E : ι → (H →L[ℂ]
G)` with `Φ = krausSumₗ E` (i.e. `Φ ρ = Σᵢ Eᵢ ρ Eᵢ†`) and the trace condition `Σᵢ Eᵢ† Eᵢ ≤ 1`
(`IsOperatorSum E Φ`).
-/
theorem satisfiesOperationAxioms_iff_isOperatorSum
    (Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)) :
    SatisfiesOperationAxioms Φ ↔
      ∃ (ι : Type) (_ : Fintype ι) (E : ι → H →L[ℂ] G), IsOperatorSum E Φ := sorry

end ContinuousLinearMap
