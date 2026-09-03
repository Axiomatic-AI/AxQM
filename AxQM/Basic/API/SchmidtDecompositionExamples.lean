/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SchmidtDecomposition
import AxQM.Basic.API.BellState
import AxQM.Basic.API.RelativePhase

/-!
# AxQM — explicit Schmidt decompositions of concrete two-qubit states (N&C Ex 2.79)

Nielsen & Chuang, Exercise 2.79 asks to **find** the Schmidt decompositions of three specific
two-qubit states. "Finding" a Schmidt decomposition means *exhibiting* it: the concrete Schmidt
coefficients `λᵢ` and orthonormal Schmidt bases `{|iᴬ⟩}`, `{|iᴮ⟩}` with
`|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.79 (state 1).** The Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`
(`bellPhiPlus`) is already in Schmidt form in the *computational* basis: its Schmidt
decomposition has two terms, with equal coefficients `λ₀ = λ₁ = 1/√2` and Schmidt bases
`|0⟩, |1⟩` on both qubits — `|Φ⁺⟩ = (1/√2)|0⟩|0⟩ + (1/√2)|1⟩|1⟩`. The coefficients are positive
and orthonormal-basis; `∑ᵢ (1/√2)² = 1`; the identity is `bellPhiPlus.vec = (√2)⁻¹ • bellVec`
expanded over `Fin 2`. (Being a two-term decomposition with the computational basis, it exhibits
the maximal entanglement of `|Φ⁺⟩`: Schmidt number 2.) -/
theorem bellPhiPlus_isSchmidtDecomposition :
    bellPhiPlus.IsSchmidtDecomposition (fun _ : Fin 2 => (Real.sqrt 2)⁻¹)
      (fun i => (qubitBasis i).vec) (fun i => (qubitBasis i).vec) := sorry

/-- **The two-qubit state `(|00⟩ + |01⟩ + |10⟩ + |11⟩)/2` of Exercise 2.79 (state 2).** Defined as
the product `|+⟩ ⊗ |+⟩` (`qubitPlus.tmul qubitPlus`), which equals
the sum-of-kets form the exercise gives. Recognising it as a product is precisely what "finding
its Schmidt decomposition" amounts to: a product state is unentangled, so the decomposition is the
single term `1 · |+⟩|+⟩`. -/
def plusPlusState : PureState (qubit ⊗ qubit) := qubitPlus.tmul qubitPlus

/-- **Nielsen & Chuang, Exercise 2.79 (state 2).** The product state
`(|00⟩ + |01⟩ + |10⟩ + |11⟩)/2 = |+⟩ ⊗ |+⟩` (`plusPlusState`) has the trivial *single-term*
Schmidt decomposition: coefficient `λ₀ = 1` and Schmidt basis `|+⟩` on both qubits,
`|+⟩ ⊗ |+⟩ = 1 · |+⟩|+⟩`. The single Schmidt coefficient (Schmidt number 1) is the hallmark of a
product state — no entanglement. Orthonormality over `Fin 1` is just the normalisation
`⟨+|+⟩ = 1`; the identity is `PureState.tmul_vec` followed by `1 • x = x`. -/
theorem plusPlusState_isSchmidtDecomposition :
    plusPlusState.IsSchmidtDecomposition (fun _ : Fin 1 => (1 : ℝ))
      (fun _ => qubitPlus.vec) (fun _ => qubitPlus.vec) := sorry

end AxQM
