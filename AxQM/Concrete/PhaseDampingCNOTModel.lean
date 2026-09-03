/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ControlledFlipOperatorSum
import AxQM.Concrete.PhaseDampingChannel
import Mathlib.Analysis.InnerProductSpace.Trace
import AxQM.ToMathlib.Analysis.InnerProductSpace.AdjointAntilinear

/-!
# Concrete: a single CNOT with a mixed environment models phase damping (N&C Exercise 8.28)

This file works, at the level of raw
operators on an arbitrary two-dimensional complex inner product space `H` (a qubit) with a chosen
computational orthonormal basis `b : OrthonormalBasis (Fin 2) ℂ H`, through Nielsen & Chuang,
*Quantum Computation and Quantum Information*, **Exercise 8.28** (p. 386).
-/

open scoped TensorProduct InnerProductSpace

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H]

variable (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The **mixed environment state** `σ_p = (1-p) |+⟩⟨+| + p |-⟩⟨-|` (N&C Exercise 8.28): the
environment enters the `±` basis as `|+⟩` with probability `1-p` and `|-⟩` with probability `p`. -/
noncomputable def phaseDampEnv (p : ℝ) : H →ₗ[ℂ] H :=
  (1 - (p : ℂ)) • qubitPlusProj b + (p : ℂ) • qubitMinusProj b

/-- The **single-CNOT phase-damping model** `E_p(ρ) = tr_env(U (ρ ⊗ σ_p) U†)` (N&C Exercise 8.28):
prepare the environment in the mixed state `σ_p = phaseDampEnv b p`, apply the controlled-flip
`U = controlledFlip b`, and discard the environment. -/
noncomputable def phaseDampCNOTChannel (p : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  LinearMap.partialTraceRight b
    (controlledFlip b ∘ₗ TensorProduct.map ρ (phaseDampEnv b p)
      ∘ₗ LinearMap.adjoint (controlledFlip b))

/-- The **phase-flip channel** `E(ρ) = (1-p) ρ + p Z ρ Z` (N&C §8.3.3/§8.3.5): with probability
`1-p` nothing happens, and with probability `p` the Pauli `Z` (a phase flip) is applied. -/
noncomputable def phaseFlipChannel (p : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  (1 - (p : ℂ)) • ρ + (p : ℂ) • (qubitPauliZ b ∘ₗ ρ ∘ₗ qubitPauliZ b)

/-- **Exercise 8.28.** The single controlled-`NOT` gate with the mixed environment `σ_p` models the
**phase-flip channel** `E_p(ρ) = (1-p) ρ + p Z ρ Z`:
`tr_env(U (ρ ⊗ σ_p) U†) = (1-p) ρ + p Z ρ Z`. -/
theorem phaseDampCNOTChannel_eq_phaseFlipChannel (p : ℝ) (ρ : H →ₗ[ℂ] H) :
    phaseDampCNOTChannel b p ρ = phaseFlipChannel b p ρ := sorry

/-- **Exercise 8.28: the mixture weight sets the amount of damping.** With the mixture
weight `p = 1 - α(λ)` (`α(λ) = phaseFlipProb λ = (1+√(1-λ))/2`), the single-CNOT model equals the
phase-damping operation elements `Ẽₖ = phaseDampKrausTilde b λ` (N&C eqs. 8.129–8.130),
for `0 ≤ λ`:
`tr_env(U (ρ ⊗ σ_{1-α}) U†) = Σₖ Ẽₖ ρ Ẽₖ†`.
So a single CNOT whose environment is the mixture `σ_{1-α(λ)}` models phase damping of parameter
`λ`, the damping increasing with the flip weight `1-α(λ) = (1-√(1-λ))/2`. -/
theorem phaseDampCNOTChannel_eq_phaseDampKrausTilde {lam : ℝ} (h0 : 0 ≤ lam) (ρ : H →ₗ[ℂ] H) :
    phaseDampCNOTChannel b (1 - phaseFlipProb lam) ρ =
      ∑ k, phaseDampKrausTilde b lam k ∘ₗ ρ ∘ₗ LinearMap.adjoint (phaseDampKrausTilde b lam k) :=
        sorry

end AxQM.Concrete
