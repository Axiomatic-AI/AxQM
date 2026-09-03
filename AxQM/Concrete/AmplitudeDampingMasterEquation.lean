/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Concrete: the amplitude-damping master equation and its operator-sum solution (N&C Problem 8.1)

At the level of `2 × 2` complex matrices, this follows Nielsen & Chuang, *Quantum Computation and
Quantum Information*, **Problem 8.1** (p. 395). The problem asks to solve the single-qubit
Lindblad (master) equation for spontaneous emission — the interaction-picture amplitude-damping
equation of §8.4.1.

## Contents

* `sigmaMinus`, `sigmaPlus` — the atomic lowering / raising operators `|0⟩⟨1|`, `|1⟩⟨0|`.
* `dampedRho lam t ρ₀` — the claimed solution `ρ(t)`, with `dampedRho_zero` the initial condition
  `ρ(0) = ρ₀`.
* `dampedRho_hasDerivAt` — `ρ(t)` **solves** the master equation: entrywise,
  `d/dt ρ(t) = lindbladGenerator lam (ρ(t))`.
* `krausAmplitudeDampingZero`, `krausAmplitudeDampingOne` — the operation elements `E₀(t)`, `E₁(t)`.
* `dampedRho_eq_kraus` — the operator-sum representation
  `ρ(t) = E₀(t) ρ(0) E₀(t)† + E₁(t) ρ(0) E₁(t)†` (for `0 ≤ λ`, `0 ≤ t`, so the damping parameter
  `γ = 1 - e^{-λt} ∈ [0, 1]` and its square root is genuine).
-/

open Matrix Complex

noncomputable section

namespace AxQM.Concrete

/-- The atomic **lowering operator** `σ₋ = |0⟩⟨1| = !![0, 1; 0, 0]` (N&C §8.4.1): it sends the
excited state `|1⟩` to the ground state `|0⟩`. -/
def sigmaMinus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The atomic **raising operator** `σ₊ = |1⟩⟨0| = !![0, 0; 1, 0]` (N&C §8.4.1), the adjoint of the
lowering operator. -/
def sigmaPlus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- The **Lindblad generator** of (8.188): the right-hand side
`-(λ/2) (σ₊σ₋ ρ + ρ σ₊σ₋ - 2 σ₋ ρ σ₊)` of the interaction-picture amplitude-damping master
equation, as a function of the density matrix `ρ`. -/
def lindbladGenerator (lam : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  -((lam : ℂ) / 2) • (sigmaPlus * sigmaMinus * ρ + ρ * (sigmaPlus * sigmaMinus)
    - (2 : ℂ) • (sigmaMinus * ρ * sigmaPlus))

/-- The claimed solution `ρ(t)` of the master equation (8.188) with initial condition `ρ₀`: the
amplitude-damped density matrix
`!![ρ₀₀ + (1 - e^{-λt}) ρ₁₁, e^{-λt/2} ρ₀₁; e^{-λt/2} ρ₁₀, e^{-λt} ρ₁₁]`. -/
def dampedRho (lam t : ℝ) (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![ρ₀ 0 0 + (1 - (Real.exp (-(lam * t)) : ℂ)) * ρ₀ 1 1, (Real.exp (-(lam * t) / 2) : ℂ) * ρ₀ 0 1;
     (Real.exp (-(lam * t) / 2) : ℂ) * ρ₀ 1 0, (Real.exp (-(lam * t)) : ℂ) * ρ₀ 1 1]

/-- **Initial condition:** at `t = 0` the solution is the initial state, `ρ(0) = ρ₀`
(`e^0 = 1`, so the damping factors are `1` and the extra `(1 - e^0) ρ₁₁` term vanishes). -/
theorem dampedRho_zero (lam : ℝ) (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) : dampedRho lam 0 ρ₀ = ρ₀ := sorry

/-- **The damped density matrix solves the master equation.** For every entry `(i, j)`, the time
derivative of `ρ(t)ᵢⱼ` equals the corresponding entry of the Lindblad generator applied to `ρ(t)`,
i.e. `d/dt ρ(t) = lindbladGenerator λ (ρ(t))` (N&C eq. 8.188). This is the differential-equation
half of Problem 8.1. -/
theorem dampedRho_hasDerivAt (lam t : ℝ) (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    HasDerivAt (fun s => dampedRho lam s ρ₀ i j)
      (lindbladGenerator lam (dampedRho lam t ρ₀) i j) t := sorry

/-- The **first operation element** `E₀(t) = diag(1, e^{-λt/2}) = diag(1, √(1-γ))` of the
amplitude-damping channel (N&C eq. 8.145), where `γ = 1 - e^{-λt}`. It leaves `|0⟩` unchanged and
shrinks the `|1⟩` amplitude, representing "no decay occurred". -/
def krausAmplitudeDampingZero (lam t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, (Real.exp (-(lam * t) / 2) : ℂ)]

/-- The **second operation element** `E₁(t) = √γ |0⟩⟨1|` of the amplitude-damping channel
(N&C eq. 8.146), where `γ = 1 - e^{-λt}`. It maps `|1⟩` to `|0⟩`, representing "a decay
(spontaneous emission) occurred". -/
def krausAmplitudeDampingOne (lam t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (Real.sqrt (1 - Real.exp (-(lam * t))) : ℂ); 0, 0]

/-- **Operator-sum (Kraus) representation** of the amplitude-damping map, N&C Problem 8.1: the
solution `ρ(t)` of the master equation is
`ρ(t) = E₀(t) ρ(0) E₀(t)† + E₁(t) ρ(0) E₁(t)†`.
The hypotheses `0 ≤ λ`, `0 ≤ t` ensure the damping parameter `γ = 1 - e^{-λt}` lies in `[0, 1]`, so
that `√γ` — the entry of `E₁` — squares back to `γ`. -/
theorem dampedRho_eq_kraus (lam t : ℝ) (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    dampedRho lam t ρ₀ =
      krausAmplitudeDampingZero lam t * ρ₀ * (krausAmplitudeDampingZero lam t)ᴴ
        + krausAmplitudeDampingOne lam t * ρ₀ * (krausAmplitudeDampingOne lam t)ᴴ := sorry

end AxQM.Concrete

end
