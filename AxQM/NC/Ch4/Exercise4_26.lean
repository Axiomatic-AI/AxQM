/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.RelativePhaseToffoli
import AxQM.Basic.API.RelativePhase

/-!
# Nielsen & Chuang, Exercise 4.26 (a Toffoli gate up to relative phases)

*(N&C p. 183.)*

Show a given circuit equals a Toffoli gate up to relative phases.

* `relativePhaseToffoliGate_relativePhaseEquiv_toffoliGate`
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.26.** On every computational-basis input `|c₁, c₂, t⟩`, the
circuit `relativePhaseToffoliGate` differs from the Toffoli gate only by a relative phase: its
output is `RelativePhaseEquiv` (in the computational-basis frame `qubitThreeBasis`) to the
Toffoli output `|c₁, c₂, t ⊕ c₁·c₂⟩`. Since the latter is a single basis vector, this says the
circuit takes `|c₁, c₂, t⟩` to `e^{iθ(c₁,c₂,t)} |c₁, c₂, t ⊕ c₁·c₂⟩` — a Toffoli gate up to
(input-dependent) phases. -/
theorem relativePhaseToffoliGate_relativePhaseEquiv_toffoliGate (c₁ c₂ t : Fin 2) :
    PureState.RelativePhaseEquiv qubitThreeBasis
      (relativePhaseToffoliGate.evolvePure (qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗ qubitBasis t)))
      (toffoliGate.evolvePure (qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗ qubitBasis t))) := sorry

end AxQM
