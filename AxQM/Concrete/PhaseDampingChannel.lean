/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QubitBasisOperators
import AxQM.ToMathlib.Analysis.InnerProductSpace.AdjointAntilinear
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Concrete: phase damping and its unitary freedom (N&C §8.3.6, Exercise 8.27)

This file defines, at the level of raw operators on an arbitrary two-dimensional complex inner
product space (a qubit) with a chosen computational orthonormal basis
`b : OrthonormalBasis (Fin 2) ℂ H`, the **phase-damping** operation elements of Nielsen & Chuang,
*Quantum Computation and Quantum Information*, §8.3.6, and proves the content of
**Exercise 8.27**: the two operator-sum representations of phase damping are related by an
explicit unitary mixing.

## Contents

* `phaseDampKrausZero b λ`, `phaseDampKrausOne b λ` — the operation elements `E₀`, `E₁`
  (eqs. 8.127–8.128), and the family `phaseDampKraus b λ = ![E₀, E₁]`.
* `phaseFlipProb λ = (1 + √(1-λ))/2` — the phase-flip "no-error" probability `α`.
* `phaseDampKrausZeroTilde λ = √α · I`, `phaseDampKrausOneTilde b λ = √(1-α)(P₀ - P₁)` — the
  recombined elements `Ẽ₀`, `Ẽ₁` (eqs. 8.129–8.130), and the family `phaseDampKrausTilde b λ`.
* `phaseDampMixingUnitary λ` — the relating matrix `u` (**the answer to Exercise 8.27**), and
  `phaseDampMixingUnitary_mem_unitaryGroup` (`u` is unitary, `0 ≤ λ ≤ 1`).
* `phaseDamp_unitaryFreedom` — **Exercise 8.27**: `Ẽₖ = Σⱼ uₖⱼ Eⱼ` for `k = 0, 1` (`0 ≤ λ ≤ 1`).
* `phaseDampChannel λ ρ = E₀ ρ E₀† + E₁ ρ E₁†` — the phase-damping channel action.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The **first phase-damping operation element** `E₀ = diag(1, √(1-λ)) = P₀ + √(1-λ) P₁`
(N&C eq. 8.127): it leaves `|0⟩` unchanged and shrinks the `|1⟩` amplitude by `√(1-λ)`, where
`λ = 1 - cos²(χΔt)` is the probability a photon of the system was scattered. -/
noncomputable def phaseDampKrausZero (lam : ℝ) : H →ₗ[ℂ] H :=
  qubitProj b 0 + (Real.sqrt (1 - lam) : ℂ) • qubitProj b 1

/-- The **second phase-damping operation element** `E₁ = diag(0, √λ) = √λ P₁` (N&C eq. 8.128):
unlike amplitude damping it destroys `|0⟩` and shrinks (does not flip) the `|1⟩` amplitude — no
energy is exchanged, only phase information is lost. -/
noncomputable def phaseDampKrausOne (lam : ℝ) : H →ₗ[ℂ] H :=
  (Real.sqrt lam : ℂ) • qubitProj b 1

/-- The phase-damping operation elements as an indexed family `![E₀, E₁]` (N&C eqs. 8.127–8.128),
the form in which the unitary-freedom relation `Ẽₖ = Σⱼ uₖⱼ Eⱼ` sums over `j`. -/
noncomputable def phaseDampKraus (lam : ℝ) : Fin 2 → (H →ₗ[ℂ] H) :=
  ![phaseDampKrausZero b lam, phaseDampKrausOne b lam]

/-- The phase-flip **"no-error" probability** `α = (1 + √(1-λ))/2` (N&C eqs. 8.129–8.130): in the
phase-flip picture of phase damping, nothing happens to the qubit with probability `α` and the Pauli
`Z` is applied with probability `1-α`. -/
noncomputable def phaseFlipProb (lam : ℝ) : ℝ := (1 + Real.sqrt (1 - lam)) / 2

/-- The **first recombined operation element** `Ẽ₀ = √α · I` (N&C eq. 8.129): with probability `α`,
phase damping leaves the qubit untouched. -/
noncomputable def phaseDampKrausZeroTilde (lam : ℝ) : H →ₗ[ℂ] H :=
  (Real.sqrt (phaseFlipProb lam) : ℂ) • LinearMap.id

/-- The **second recombined operation element** `Ẽ₁ = √(1-α) · Z = √(1-α)(P₀ - P₁)`
(N&C eq. 8.130): with probability `1-α`, phase damping applies the Pauli `Z` (a phase flip). -/
noncomputable def phaseDampKrausOneTilde (lam : ℝ) : H →ₗ[ℂ] H :=
  (Real.sqrt (1 - phaseFlipProb lam) : ℂ) • (qubitProj b 0 - qubitProj b 1)

/-- The recombined phase-flip operation elements as an indexed family `![Ẽ₀, Ẽ₁]`
(N&C eqs. 8.129–8.130). -/
noncomputable def phaseDampKrausTilde (lam : ℝ) : Fin 2 → (H →ₗ[ℂ] H) :=
  ![phaseDampKrausZeroTilde lam, phaseDampKrausOneTilde b lam]

/-- **The answer to Exercise 8.27**: the `2 × 2` unitary `u = !![√α, √(1-α); √(1-α), -√α]` relating
the two sets of phase-damping operation elements via `Ẽₖ = Σⱼ uₖⱼ Eⱼ` (`α = phaseFlipProb λ`). It is
real, symmetric and orthogonal — a reflection. Note `u` mixes the *index* `{0,1}` of the operation
elements, hence is a `Matrix (Fin 2) (Fin 2) ℂ`, not an operator on the qubit. -/
noncomputable def phaseDampMixingUnitary (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt (phaseFlipProb lam) : ℂ), (Real.sqrt (1 - phaseFlipProb lam) : ℂ);
     (Real.sqrt (1 - phaseFlipProb lam) : ℂ), -(Real.sqrt (phaseFlipProb lam) : ℂ)]

/-- `u ∈ unitaryGroup` (`0 ≤ λ`): the "unitary" half of Exercise 8.27. -/
theorem phaseDampMixingUnitary_mem_unitaryGroup {lam : ℝ} (h0 : 0 ≤ lam) :
    phaseDampMixingUnitary lam ∈ Matrix.unitaryGroup (Fin 2) ℂ := sorry

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **Exercise 8.27**: the recombined phase-flip operation elements are the unitary mixing `Ẽₖ = Σⱼ
uₖⱼ Eⱼ` of the phase-damping operation elements, for `k = 0, 1` and `0 ≤ λ ≤ 1`.
-/
theorem phaseDamp_unitaryFreedom {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (k : Fin 2) :
    phaseDampKrausTilde b lam k
      = ∑ j, phaseDampMixingUnitary lam k j • phaseDampKraus b lam j := sorry

/-- The **phase-damping channel** `E_PD(ρ) = E₀ ρ E₀† + E₁ ρ E₁†` (N&C §8.3.6): the quantum
operation with operation elements `E₀ = diag(1, √(1-λ))` and `E₁ = diag(0, √λ)` (eqs.
8.127–8.128). -/
noncomputable def phaseDampChannel (lam : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  phaseDampKrausZero b lam ∘ₗ ρ ∘ₗ LinearMap.adjoint (phaseDampKrausZero b lam)
    + phaseDampKrausOne b lam ∘ₗ ρ ∘ₗ LinearMap.adjoint (phaseDampKrausOne b lam)

end AxQM.Concrete

end
