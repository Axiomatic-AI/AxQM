/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledReduction
import AxQM.Concrete.Rotation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.Qubit

/-!
# Nielsen & Chuang, Exercise 4.28 — a `C⁵(U)` gate for `U = V²` using no work qubits

*(N&C p. 184.)*

For U=V^2, construct a C^5(U) gate using no work qubits via controlled-V,V-dagger.

* `barenco5Circuit`
* `exists_barenco5Circuit_eq_mcCtrl`
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The Exercise 4.28 circuit** for `C⁵(U)`, `U = V₁²`, with no work qubits. It is the four-level
Barenco reduction with every leading multiplexer recursively expanded. Every gate is
single-qubit-controlled (`C(Vⱼ)`, `C(Vⱼ†)`) or a multiply-controlled `NOT` (`Cᵏ(X)`); all act on
the six-qubit register `qtower 4 (qubit ⊗ qubit)` with no ancilla. -/
def barenco5Circuit (V₁ V₂ V₃ V₄ : Evolution qubit) : Evolution (qtower 4 (qubit ⊗ qubit)) :=
  (((barencoReductionCircuit 1 (((V₄.onRight qubit).onRight qubit).onRight qubit)).comp
        (barencoTail 2 ((V₃.onRight qubit).onRight qubit))).comp
      (barencoTail 3 (V₂.onRight qubit))).comp
    (barencoTail 4 V₁)

/-- **Nielsen & Chuang, Exercise 4.28 (existence, fully faithful).** For *every* single-qubit
unitary `V` — so `U = V²` — there is a no-work-qubit circuit `barenco5Circuit V V₂ V₃ V₄` equal to
`C⁵(U)`, built only from single-qubit-controlled gates (`C(V), C(V†), …, C(V₄), C(V₄†)`) and
multiply-controlled `NOT`s. No square-root hypotheses are imposed beyond the exercise's own
`U = V²`. Here `C⁵(U) = mcCtrl 5 (V.comp V)` (five controls onto the qubit target, no ancilla). -/
theorem exists_barenco5Circuit_eq_mcCtrl (V : Evolution qubit) :
    ∃ V₂ V₃ V₄ : Evolution qubit, mcCtrl 5 (V.comp V) = barenco5Circuit V V₂ V₃ V₄ := sorry

end AxQM
