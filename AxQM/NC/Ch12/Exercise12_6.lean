/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Fidelity
import AxQM.Basic.API.TraceDistance
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
import AxQM.Concrete.ClassicalTraceDistance
import AxQM.Basic.API.PureState
import AxQM.Basic.PiTensorState
import AxQM.Basic.API.HadamardABC
import AxQM.Basic.API.Qubit
import AxQM.Basic.PartialTrace
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.Purification
import AxQM.Basic.API.Evolution
import AxQM.ToMathlib.Analysis.InnerProductSpace.EuclideanConjVec
import AxQM.ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl
import AxQM.Basic.API.ControlledRotation
import AxQM.Basic.API.ControlledControlledUnitary
import Mathlib.InformationTheory.Hamming

/-!
# Nielsen & Chuang, Exercise 12.6 — the coefficients `C_X` of Schumacher's Box 12.4

*(N&C p. 546.)*

Give explicit C_X for Box 12.4; construct circuit for U_n; count elementary ops.

* `schumacherTypicalKet`, `schumacherSourceKet` — the typical basis `|b̄⟩`
  and sources `|ψ_k⟩`;
* `schumacherBlock_overlap` — the exact block coefficient `C_X = ∏ᵢ ⟨x̄ᵢ | ψ_{kᵢ}⟩`;
* `schumacherBlock_fidelity` — `|C_X| = cos(π/8)^{n−w} sin(π/8)^{w}`.
-/

open scoped InnerProductSpace BigOperators

noncomputable section

namespace AxQM

/-- **The Schumacher typical basis of Box 12.4:** `|b̄⟩ = R_y(π/4)|b⟩`, i.e.
`|0̄⟩ = cos(π/8)|0⟩ + sin(π/8)|1⟩` and `|1̄⟩ = −sin(π/8)|0⟩ + cos(π/8)|1⟩`, the orthonormal
eigenbasis of the source density operator `ρ = ¼!![3,1;1,1]`. -/
def schumacherTypicalKet (b : Fin 2) : PureState qubit :=
  (rotYGate (Real.pi / 4)).evolvePure (qubitBasis b)

/-- **The Schumacher source states of Box 12.4:** `|ψ₀⟩ = |0⟩` and
`|ψ₁⟩ = R_y(π/2)|0⟩ = (|0⟩ + |1⟩)/√2 = |+⟩`, emitted with equal probabilities. -/
def schumacherSourceKet : Fin 2 → PureState qubit :=
  ![qubitBasis 0, (rotYGate (Real.pi / 2)).evolvePure (qubitBasis 0)]

/-- **The exact block coefficient `C_X` of Box 12.4.** For a source block `|Ψ⟩ = |ψ_{k₁}⟩ ⊗ ⋯ ⊗
|ψ_{kₙ}⟩` and a typical-basis label `X = x₁…xₙ`, the coefficient `C_X = ⟨X | Ψ⟩` factorizes over
the tensor factors as the product of the single-qubit amplitudes, `C_X = ∏ᵢ ⟨x̄ᵢ | ψ_{kᵢ}⟩` —
the "explicit expression for `C_X` in terms of `X`" the exercise asks for. -/
theorem schumacherBlock_overlap {n : ℕ} (x k : Fin n → Fin 2) :
    (PureState.piTensor fun i => schumacherTypicalKet (x i)).overlap
        (PureState.piTensor fun i => schumacherSourceKet (k i))
      = ∏ i, (schumacherTypicalKet (x i)).overlap (schumacherSourceKet (k i)) := sorry

/-- **Nielsen & Chuang, Exercise 12.6 (Box 12.4): the magnitude of the block coefficient `C_X`.**
For a source block `|Ψ⟩ = |ψ_{k₁}⟩ ⊗ ⋯ ⊗ |ψ_{kₙ}⟩` (any realisation `k : Fin n → Fin 2` of the
source) and a typical-basis label `X = x₁…xₙ` (`x : Fin n → Fin 2`), the magnitude of the
coefficient `C_X = ⟨X | Ψ⟩` is

`|C_X| = F(|X⟩, |Ψ⟩) = cos(π/8)^{n − w(X)} · sin(π/8)^{w(X)}`,

where `w(X) = hammingNorm x` is the Hamming weight of the label (the number of `1̄` entries).
The magnitude is **independent of the source realisation `k`** and decays exponentially in
`w(X)` (since `sin(π/8) < cos(π/8)`): this is precisely the box's statement that the
coefficients `C_X` are very small for `X` of large Hamming weight, hence only the low-weight
(typical) labels carry appreciable weight — the basis of Schumacher compression.
-/
theorem schumacherBlock_fidelity {n : ℕ} (x k : Fin n → Fin 2) :
    (PureState.piTensor fun i => schumacherTypicalKet (x i)).toState.fidelity
        (PureState.piTensor fun i => schumacherSourceKet (k i)).toState
      = Real.cos (Real.pi / 8) ^ (n - hammingNorm x) * Real.sin (Real.pi / 8) ^ hammingNorm x :=
        sorry

end AxQM
