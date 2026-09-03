/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Qubit
import AxQM.Basic.Composite
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Basic.API — the three-qubit computational basis

The computational basis of the three-qubit register `qubit ⊗ (qubit ⊗ qubit)`, its
orthonormality, and extensionality for operators on it.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The computational basis of the three-qubit system** `qubit ⊗ (qubit ⊗ qubit)`, as a family of
pure states indexed by the bit string `(q₁, q₂, q₃)`: `|q₁, q₂, q₃⟩ = |q₁⟩ ⊗ (|q₂⟩ ⊗ |q₃⟩)`. -/
def qubitThreeBasis : Fin 2 × Fin 2 × Fin 2 → PureState (qubit ⊗ (qubit ⊗ qubit)) :=
  fun i => qubitBasis i.1 ⊗ (qubitBasis i.2.1 ⊗ qubitBasis i.2.2)

/-- The **three-qubit computational basis** as a `Module.Basis`, the tensor product of three copies
of the single-qubit `qubitModuleBasis`. -/
noncomputable def qubitThreeModuleBasis :
    Module.Basis (Fin 2 × Fin 2 × Fin 2) ℂ (qubit.space ⊗[ℂ] (qubit.space ⊗[ℂ] qubit.space)) :=
  qubitModuleBasis.tensorProduct (qubitModuleBasis.tensorProduct qubitModuleBasis)

/-- The basis vector at `(q₁, q₂, q₃)` is the computational ket `|q₁q₂q₃⟩`. -/
theorem qubitThreeModuleBasis_apply (b : Fin 2 × Fin 2 × Fin 2) :
    qubitThreeModuleBasis b = (qubitThreeBasis b).vec := by
  obtain ⟨b1, b2, b3⟩ := b
  rw [qubitThreeModuleBasis, Module.Basis.tensorProduct_apply', Module.Basis.tensorProduct_apply',
    qubitModuleBasis_apply, qubitModuleBasis_apply, qubitModuleBasis_apply]
  rfl

/-- **Extensionality on the computational basis:** two operators on the three-qubit register are
equal once they agree on every computational basis ket `|q₁q₂q₃⟩`. -/
theorem qubitThree_op_ext {T1 T2 : (qubit ⊗ (qubit ⊗ qubit)).space →L[ℂ]
    (qubit ⊗ (qubit ⊗ qubit)).space}
    (h : ∀ b : Fin 2 × Fin 2 × Fin 2, T1 (qubitThreeBasis b).vec = T2 (qubitThreeBasis b).vec) :
    T1 = T2 := by
  apply ContinuousLinearMap.coe_injective
  apply Module.Basis.ext qubitThreeModuleBasis
  intro b
  rw [qubitThreeModuleBasis_apply]
  exact h b

/-- **The three-qubit computational basis kets are orthonormal.** -/
theorem qubitThreeBasis_orthonormal : Orthonormal ℂ (fun b => (qubitThreeBasis b).vec) := by
  rw [show (fun b => (qubitThreeBasis b).vec) = ⇑qubitThreeModuleBasis from
    funext fun b => (qubitThreeModuleBasis_apply b).symm]
  exact qubitModuleBasis_orthonormal.basisTensorProduct
    (qubitModuleBasis_orthonormal.basisTensorProduct qubitModuleBasis_orthonormal)

/-- **A rank-one projector onto a basis ket acts as a Kronecker delta:**
`|s⟩⟨s| · |b⟩ = δ_{s,b} |s⟩`. -/
theorem qubitThreeBasis_rankOne_apply (s b : Fin 2 × Fin 2 × Fin 2) :
    (rankOne ℂ (qubitThreeBasis s).vec (qubitThreeBasis s).vec) (qubitThreeBasis b).vec
      = (if s = b then (1 : ℂ) else 0) • (qubitThreeBasis s).vec := by
  rw [InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp qubitThreeBasis_orthonormal s b]

end AxQM
