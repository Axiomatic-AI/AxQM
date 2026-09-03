/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QubitBasisOperators
import AxQM.ToMathlib.Analysis.InnerProductSpace.AdjointAntilinear
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Concrete: the amplitude-damping channel on an abstract qubit (N&C §8.3.5)

The **amplitude-damping channel** of Nielsen & Chuang, *Quantum Computation and Quantum
Information*, §8.3.5 (eqs. 8.107, 8.108), with damping parameter `γ`, on a two-dimensional complex
inner product space (a qubit) with a chosen computational orthonormal basis
`b : OrthonormalBasis (Fin 2) ℂ H`.

## Contents

* `ampDampKrausZero b γ`, `ampDampKrausOne b γ` — the operation elements `E₀`, `E₁` (eq. 8.108).
* `ampDampChannel b γ ρ` — the amplitude-damping channel `E_AD(ρ) = E₀ ρ E₀† + E₁ ρ E₁†`
  (N&C eq. 8.107).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The **first operation element** `E₀ = |0⟩⟨0| + √(1-γ) |1⟩⟨1| = diag(1, √(1-γ))` of the
amplitude-damping channel (N&C eq. 8.108): it leaves `|0⟩` unchanged and shrinks the `|1⟩` amplitude
by `√(1-γ)` (no quantum of energy was lost). -/
noncomputable def ampDampKrausZero (γ : ℝ) : H →ₗ[ℂ] H :=
  qubitProj b 0 + (Real.sqrt (1 - γ) : ℂ) • qubitProj b 1

/-- The **second operation element** `E₁ = √γ |0⟩⟨1| = √γ σ₋` of the amplitude-damping channel
(N&C eq. 8.108): it maps `|1⟩` to `|0⟩` with amplitude `√γ` (a quantum of energy was lost to the
environment). -/
noncomputable def ampDampKrausOne (γ : ℝ) : H →ₗ[ℂ] H :=
  (Real.sqrt γ : ℂ) • qubitLower b

/-- The **amplitude-damping channel** `E_AD(ρ) = E₀ ρ E₀† + E₁ ρ E₁†` (N&C eq. 8.107): the quantum
operation with operation elements `E₀ = diag(1, √(1-γ))` and `E₁ = √γ |0⟩⟨1|`. -/
noncomputable def ampDampChannel (γ : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  ampDampKrausZero b γ ∘ₗ ρ ∘ₗ LinearMap.adjoint (ampDampKrausZero b γ)
    + ampDampKrausOne b γ ∘ₗ ρ ∘ₗ LinearMap.adjoint (ampDampKrausOne b γ)

end AxQM.Concrete

end
