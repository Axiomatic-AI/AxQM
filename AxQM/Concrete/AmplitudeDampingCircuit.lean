/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingChannel
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# Concrete: the Figure 8.13 circuit models amplitude damping (N&C Exercise 8.20)

Working at the level of raw operators on an arbitrary two-dimensional complex inner product space
`H` (a qubit) with a chosen computational orthonormal basis `b : OrthonormalBasis (Fin 2) ℂ H`,
Nielsen & Chuang, *Quantum Computation and Quantum Information*, **Exercise 8.20** (p. 380–381)
asks to show that the **Figure 8.13 circuit** models the amplitude-damping quantum operation, with
`sin²(θ/2) = γ`.

## Contents

* `qubitRotYGen b`, `qubitRotY b θ` — the `y`-rotation generator `G = |1⟩⟨0| - |0⟩⟨1|` and the
  single-qubit rotation `R_y(θ) = cos(θ/2) I + sin(θ/2) G`.
* `ampDampCRy b θ`, `ampDampCNOT b` — the controlled-`R_y` and CNOT gates, each unitary.
* `ampDampCircuitDilation b θ = U (· ⊗ |0⟩)` — the dilation `V`.
* `ampDampCircuitChannel b θ ρ = tr_env(V ρ V†)`, with **the answer**
  `ampDampCircuit_reduced_eq_ampDampChannel : ampDampCircuitChannel b θ ρ = ampDampChannel b
  (sin²(θ/2)) ρ` (for `0 ≤ θ ≤ π`).
-/

open scoped TensorProduct InnerProductSpace

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The **`y`-rotation generator** `G = σ₊ - σ₋ = |1⟩⟨0| - |0⟩⟨1|`. -/
noncomputable def qubitRotYGen : H →ₗ[ℂ] H :=
  (InnerProductSpace.rankOne ℂ (b 1) (b 0) : H →ₗ[ℂ] H)
    - (InnerProductSpace.rankOne ℂ (b 0) (b 1) : H →ₗ[ℂ] H)

/-- The single-qubit **`y`-axis rotation** `R_y(θ) = exp(-iθY/2) = cos(θ/2) I + sin(θ/2) G`
(N&C §4.2), with `G = |1⟩⟨0| - |0⟩⟨1|` the rotation generator. It sends
`|0⟩ ↦ cos(θ/2)|0⟩ + sin(θ/2)|1⟩` and `|1⟩ ↦ -sin(θ/2)|0⟩ + cos(θ/2)|1⟩`. -/
noncomputable def qubitRotY (θ : ℝ) : H →ₗ[ℂ] H :=
  (Real.cos (θ / 2) : ℂ) • LinearMap.id + (Real.sin (θ / 2) : ℂ) • qubitRotYGen b

/-- The **controlled-`R_y(θ)`** gate `P₀ ⊗ I + P₁ ⊗ R_y(θ)` (N&C Fig. 8.13): the system (left
factor) controls a `y`-rotation of the environment (right factor). -/
noncomputable def ampDampCRy (θ : ℝ) : H ⊗[ℂ] H →ₗ[ℂ] H ⊗[ℂ] H :=
  TensorProduct.map (qubitProj b 0) LinearMap.id
    + TensorProduct.map (qubitProj b 1) (qubitRotY b θ)

/-- The **CNOT** gate `I ⊗ P₀ + X ⊗ P₁` (N&C Fig. 8.13): the environment (right factor) controls a
bit-flip of the system (left factor). -/
noncomputable def ampDampCNOT : H ⊗[ℂ] H →ₗ[ℂ] H ⊗[ℂ] H :=
  TensorProduct.map LinearMap.id (qubitProj b 0)
    + TensorProduct.map (qubitFlip b) (qubitProj b 1)

/-- The **Figure 8.13 circuit** unitary `U = CNOT ∘ CRy(θ)`: prepare the environment in `|0⟩`, apply
the controlled rotation, then the CNOT. -/
noncomputable def ampDampCircuit (θ : ℝ) : H ⊗[ℂ] H →ₗ[ℂ] H ⊗[ℂ] H :=
  ampDampCNOT b ∘ₗ ampDampCRy b θ

/-- The **dilation** `V = U (· ⊗ |0⟩) : H →ₗ H ⊗ H`: prepare the environment in `|0⟩`, then apply
the Figure 8.13 unitary. -/
noncomputable def ampDampCircuitDilation (θ : ℝ) : H →ₗ[ℂ] H ⊗[ℂ] H :=
  ampDampCircuit b θ ∘ₗ LinearMap.embedRight b 0

/-- The **quantum operation modelled by the circuit**, in dilation form
`E(ρ) = tr_env(V ρ V†)`. -/
noncomputable def ampDampCircuitChannel (θ : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  LinearMap.partialTraceRight b
    (ampDampCircuitDilation b θ ∘ₗ ρ ∘ₗ LinearMap.adjoint (ampDampCircuitDilation b θ))

omit [CompleteSpace H] in
/-- **N&C Exercise 8.20 (the answer):** the Figure 8.13 circuit models amplitude damping with `γ =
sin²(θ/2)`. Tracing the environment out of the circuit's closed evolution returns exactly the
amplitude-damping channel `E_AD` at `γ = sin²(θ/2)`:

`tr_env(U (ρ ⊗ |0⟩⟨0|) U†) = E_AD(ρ)`,   for `0 ≤ θ ≤ π`.
-/
theorem ampDampCircuit_reduced_eq_ampDampChannel (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (ρ : H →ₗ[ℂ] H) :
    ampDampCircuitChannel b θ ρ = ampDampChannel b (Real.sin (θ / 2) ^ 2) ρ := sorry

end AxQM.Concrete

end
