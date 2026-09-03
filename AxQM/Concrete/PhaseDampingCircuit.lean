/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingCircuit
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# Concrete: circuit model for phase damping (N&C Exercise 8.26, Figure 8.15)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, **Exercise 8.26** (p. 385), at the
level of raw operators on a two-dimensional complex inner product space (a qubit). A *principal
system*
(control) and an *environment* (target) prepared in `|0⟩` interact through the
**controlled-`Rᵧ(θ)`** gate of Figure 8.15.
-/

open scoped TensorProduct InnerProductSpace

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The **first phase-damping operation element** `E₀ = diag(1, √(1-λ)) = |0⟩⟨0| + √(1-λ)|1⟩⟨1|`
(N&C eq. 8.127). This is the *same* diagonal operator as amplitude damping's `E₀` (eq. 8.108); only
the second element differs between the two channels. -/
def phaseDampingKrausZero (lam : ℝ) : H →ₗ[ℂ] H := ampDampKrausZero b lam

/-- The **second phase-damping operation element** `E₁ = diag(0, √λ) = √λ |1⟩⟨1|` (N&C eq. 8.128):
unlike amplitude damping's `√λ |0⟩⟨1|`, it does *not* move `|1⟩` to `|0⟩` (no energy is lost); it
only scales the excited amplitude, dephasing the coherences. -/
def phaseDampingKrausOne (lam : ℝ) : H →ₗ[ℂ] H := (Real.sqrt lam : ℂ) • qubitProj b 1

/-- The **phase-damping channel** `E(ρ) = E₀ ρ E₀† + E₁ ρ E₁†`, the target of the Figure 8.15
circuit model. -/
def phaseDampingChannel (lam : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  phaseDampingKrausZero b lam ∘ₗ ρ ∘ₗ LinearMap.adjoint (phaseDampingKrausZero b lam)
    + phaseDampingKrausOne b lam ∘ₗ ρ ∘ₗ LinearMap.adjoint (phaseDampingKrausOne b lam)

/-- The **dilation** `V = U(· ⊗ |0⟩) : H →ₗ H ⊗ H` of the Figure 8.15 circuit: prepare the
environment in `|0⟩`, then apply the controlled-`Rᵧ(θ)` interaction `U = P₀ ⊗ I + P₁ ⊗ Rᵧ(θ)`. -/
def phaseDampingCircuitDilation (θ : ℝ) : H →ₗ[ℂ] H ⊗[ℂ] H :=
  ampDampCRy b θ ∘ₗ LinearMap.embedRight b 0

/-- The **circuit operation** `E_θ(ρ) = tr_env(V ρ V†)` induced by the Figure 8.15 circuit. -/
def phaseDampingCircuitOperation (θ : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  LinearMap.partialTraceRight b
    (phaseDampingCircuitDilation b θ ∘ₗ ρ ∘ₗ LinearMap.adjoint (phaseDampingCircuitDilation b θ))

/-- **Exercise 8.26 (θ chosen appropriately).** For *any* phase-damping parameter `λ ∈ [0,1]` there
is an angle `θ ∈ [0,π]` for which the Figure 8.15 circuit realizes the phase-damping channel with
parameter `λ`. This is the exercise's "provided `θ` is chosen appropriately". -/
theorem phaseDampingCircuit_models_phaseDamping (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ Real.pi ∧
      ∀ ρ : H →ₗ[ℂ] H, phaseDampingCircuitOperation b θ ρ = phaseDampingChannel b lam ρ := sorry

end AxQM.Concrete

end
