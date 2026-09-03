/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary

/-!
# AxQM.Basic.API — the three-qubit bit-flip code: input, encoder, codeword

* `qubitSuperposition a b h` — the general single-qubit pure state `a|0⟩ + b|1⟩`, for amplitudes
  `a, b : ℂ` with `‖a‖² + ‖b‖² = 1`. This is the input qubit of Exercise 10.1.
* `bitFlipEncode` — the encoding circuit of Figure 10.2 as an `Evolution` on
  `qubit ⊗ qubit ⊗ qubit`: the composite of the two CNOTs of the figure, both controlled by the
  data qubit,
  `CNOT₁₂ = C(X ⊗ 1)` and `CNOT₁₃ = C(1 ⊗ X)`, each realised through the general controlled-`U` gate
  `controlledUnitary` (N&C §4.3).
* `bitFlipCodeword a b h` — the encoded logical state `a|000⟩ + b|111⟩` (the logical codewords
  `|0_L⟩ = |000⟩` and `|1_L⟩ = |111⟩` superposed).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Normalized superposition of an orthonormal pair.** For pure states `ψ, φ` of a system `S`
whose vectors are orthogonal (`⟨ψ|φ⟩ = 0`) and amplitudes `a, b : ℂ` with `‖a‖² + ‖b‖² = 1`, the
vector `a • ψ.vec + b • φ.vec` is a unit vector, hence a genuine `PureState`. -/
def PureState.orthoPair (ψ φ : PureState S) (hortho : inner ℂ ψ.vec φ.vec = 0)
    (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : PureState S where
  vec := a • ψ.vec + b • φ.vec
  normalized := by
    have hab : inner ℂ (a • ψ.vec) (b • φ.vec) = (0 : ℂ) := by
      rw [inner_smul_left, inner_smul_right, hortho, mul_zero, mul_zero]
    have hsq : ‖a • ψ.vec + b • φ.vec‖ ^ 2 = 1 := by
      rw [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hab]
      simp only [norm_smul, ψ.normalized, φ.normalized, mul_one]
      rw [← pow_two, ← pow_two]; exact h
    rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one]

/-- **`PureState.orthoPair` over the primitives.** Identical to `PureState.orthoPair`, but takes the
orthogonality hypothesis as the vanishing of the overlap (`ψ.overlap φ = 0`) rather than the raw
`inner ⟪ψ.vec, φ.vec⟫ = 0`. -/
def PureState.orthoPairOfOverlap (ψ φ : PureState S) (h : ψ.overlap φ = 0)
    (a b : ℂ) (hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : PureState S :=
  PureState.orthoPair ψ φ (by rw [← PureState.overlap_def]; exact h) a b hab

/-- The equal-weight amplitude `(√2)⁻¹ : ℂ` has squared modulus `‖(√2)⁻¹‖² = ½`. -/
theorem norm_sq_sqrtTwo_inv : ‖(Real.sqrt 2 : ℂ)⁻¹‖ ^ 2 = 2⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2), inv_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- The **general single-qubit pure state `a|0⟩ + b|1⟩`**, for amplitudes `a, b : ℂ` satisfying the
normalization `‖a‖² + ‖b‖² = 1`. This is the input qubit of Exercise 10.1. -/
def qubitSuperposition (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : PureState qubit :=
  PureState.orthoPair (qubitBasis 0) (qubitBasis 1)
    (by rw [qubitBasis_inner_qubitBasis]; simp) a b h

/-- **The encoding circuit of Figure 10.2** as an `Evolution` on the three-qubit system
`qubit ⊗ qubit ⊗ qubit`: the composite of the two CNOTs of the figure, both controlled by the data
qubit (qubit 1). `CNOT₁₂ = C(X ⊗ 1)` flips ancilla qubit 2, and `CNOT₁₃ = C(1 ⊗ X)` flips ancilla
qubit 3, each realised as the controlled-`U` gate `controlledUnitary` (N&C §4.3) with the Pauli-`X`
gate on the targeted ancilla. Because the two CNOTs share their control and act on disjoint targets,
they commute and the composite is order-independent. -/
def bitFlipEncode : Evolution (qubit ⊗ qubit ⊗ qubit) :=
  (controlledUnitary (pauliXGate ⊗ (Evolution.id : Evolution qubit))).comp
    (controlledUnitary ((Evolution.id : Evolution qubit) ⊗ pauliXGate))

/-- **The three-qubit bit-flip codeword `a|000⟩ + b|111⟩`**, for amplitudes `a, b : ℂ` with `‖a‖² +
‖b‖² = 1`. This is the output of the encoding circuit. -/
def bitFlipCodeword (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    PureState (qubit ⊗ qubit ⊗ qubit) :=
  PureState.orthoPair (qubitBasis 0 ⊗ qubitBasis 0 ⊗ qubitBasis 0)
    (qubitBasis 1 ⊗ qubitBasis 1 ⊗ qubitBasis 1)
    (by
      rw [PureState.tmul_vec, PureState.tmul_vec]
      change inner ℂ ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0 ⊗ qubitBasis 0).vec)
          ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1 ⊗ qubitBasis 1).vec) = 0
      rw [TensorProduct.inner_tmul ℂ, qubitBasis_inner_qubitBasis]; simp)
    a b h

end AxQM
