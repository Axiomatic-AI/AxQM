/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary
import Mathlib.Analysis.InnerProductSpace.PiL2
import AxQM.Basic.API.Fidelity
import AxQM.Basic.API.TraceDistance
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
import AxQM.Concrete.ClassicalTraceDistance

/-!
# Nielsen & Chuang, Exercise 12.1 — copying two orthogonal qubit states

*(N&C p. 530.)*

Design a 2-qubit circuit copying orthogonal single-qubit states |psi>,|phi>.

* `exists_orthogonalCloningCircuit`
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 12.1: orthogonal single-qubit states can be cloned.** For two
orthogonal pure states `|ψ⟩`, `|φ⟩` of a qubit — orthogonality expressed as the vanishing
fidelity `F(ψ, φ) = 0` — there exists a two-qubit unitary evolution `U` (the "copying circuit",
the data qubit as control and a `|0⟩` target) that copies both: `U(|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩` and
`U(|φ⟩ ⊗ |0⟩) = |φ⟩ ⊗ |φ⟩`. -/
theorem exists_orthogonalCloningCircuit (ψ φ : PureState qubit)
    (h : ψ.toState.fidelity φ.toState = 0) :
    ∃ U : Evolution (qubit ⊗ qubit),
      U.evolvePure (ψ.tmul (qubitBasis 0)) = ψ.tmul ψ ∧
      U.evolvePure (φ.tmul (qubitBasis 0)) = φ.tmul φ := sorry

end AxQM
