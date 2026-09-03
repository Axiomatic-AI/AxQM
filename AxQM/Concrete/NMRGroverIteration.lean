/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ABCDecomposition
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Concrete: simplifying the NMR Grover iteration (Nielsen & Chuang, Exercise 7.51)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §7.7.4 (p. 339–340) describe the
two-qubit (`N = 4`) Grover search realised on an NMR quantum computer. Each of the three ingredients
of the **Grover iteration** `G = H^{⊗2} · P · H^{⊗2} · O` is expressed as single-qubit rotation
pulses `R_x, R_y` (`R = R(π/2)`, `R̄ = R(−π/2)`, `R² = R(π)`) plus one free-`J`-coupling period
`τ = e^{−iH/2ℏJ}`.

## Main results
* `nmrGroverIteration_markedThree` (`x₀ = 3`) and `nmrGroverIteration_markedZero` (`x₀ = 0`) are
  **exact** matrix identities `G = nmrGroverIterationSimplified …`;
* `nmrGroverIteration_markedTwo` (`x₀ = 2`) and `nmrGroverIteration_markedOne` (`x₀ = 1`) are
  `G = −(nmrGroverIterationSimplified …)`.
-/

noncomputable section

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

/-- The per-qubit **Hadamard pulse** `H = R²_x R̄_y = R_x(π) R_y(−π/2)` (N&C p. 339). -/
def nmrHadamardPulse : Matrix (Fin 2) (Fin 2) ℂ := rotX Real.pi * rotY (-(Real.pi / 2))

/-- The per-qubit **`R_y R_x(s) R̄_y` sandwich** `= R_y(π/2) R_x(s) R_y(−π/2)`. -/
def nmrRotYXY (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rotY (Real.pi / 2) * rotX s * rotY (-(Real.pi / 2))

/-- `H^{⊗2} = H ⊗ H`, the two-qubit Hadamard as a Kronecker product of the per-qubit pulse. -/
def nmrHadamardPair : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  nmrHadamardPulse ⊗ₖ nmrHadamardPulse

/-- The **conditional phase-shift** `P = (R_y R_x R̄_y)^{⊗2} τ` (Nielsen & Chuang eq. 7.171 in pulse
form), with the free-`J`-evolution period `τ` a parameter. -/
def nmrPhaseShiftPulse (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (nmrRotYXY (Real.pi / 2) ⊗ₖ nmrRotYXY (Real.pi / 2)) * τ

/-- The **oracle** `O = (R_y R_x(s₁) R̄_y ⊗ R_y R_x(s₂) R̄_y) τ` for the marked item with per-qubit
`x`-rotation angles `s₁, s₂` (each `−π/2` on a marked bit, `+π/2` on an unmarked bit). -/
def nmrOraclePulse (s₁ s₂ : ℝ) (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (nmrRotYXY s₁ ⊗ₖ nmrRotYXY s₂) * τ

/-- The **Grover iteration** `G = H^{⊗2} P H^{⊗2} O`, in NMR pulse form, for the oracle whose
per-qubit `x`-rotation angles are `s₁, s₂`. -/
def nmrGroverIteration (s₁ s₂ : ℝ) (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  nmrHadamardPair * nmrPhaseShiftPulse τ * nmrHadamardPair * nmrOraclePulse s₁ s₂ τ

/-- The **simplified Grover iteration** — the right-hand side of Nielsen & Chuang (7.172). -/
def nmrGroverIterationSimplified (a₁ a₂ : ℝ) (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((rotX (-(Real.pi / 2)) * rotY (-(Real.pi / 2)))
        ⊗ₖ (rotX (-(Real.pi / 2)) * rotY (-(Real.pi / 2)))) * τ
    * ((rotX a₁ * rotY (-(Real.pi / 2))) ⊗ₖ (rotX a₂ * rotY (-(Real.pi / 2)))) * τ

/-- **Exercise 7.51, `x₀ = 3 = |11⟩`.** With both qubits marked (`s₁ = s₂ = −π/2`) the Grover
iteration equals its simplified form *exactly* (no residual phase):
`G = (R̄_x R̄_y)^{⊗2} τ · (R_x R̄_y)^{⊗2} τ`. -/
theorem nmrGroverIteration_markedThree (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    nmrGroverIteration (-(Real.pi / 2)) (-(Real.pi / 2)) τ
      = nmrGroverIterationSimplified (Real.pi / 2) (Real.pi / 2) τ := sorry

/-- **Exercise 7.51, `x₀ = 0 = |00⟩`.** With neither qubit marked (`s₁ = s₂ = +π/2`) the Grover
iteration again equals its simplified form *exactly*:
`G = (R̄_x R̄_y)^{⊗2} τ · (R̄_x R̄_y)^{⊗2} τ`. -/
theorem nmrGroverIteration_markedZero (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    nmrGroverIteration (Real.pi / 2) (Real.pi / 2) τ
      = nmrGroverIterationSimplified (-(Real.pi / 2)) (-(Real.pi / 2)) τ := sorry

/-- **Exercise 7.51, `x₀ = 2 = |10⟩`.** Qubit 1 marked (`s₁ = −π/2`), qubit 2 unmarked
(`s₂ = +π/2`): the Grover iteration equals its simplified form up to the overall "irrelevant"
phase `−1`: `G = −((R̄_x R̄_y)^{⊗2} τ · (R_x R̄_y ⊗ R̄_x R̄_y) τ)`. -/
theorem nmrGroverIteration_markedTwo (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    nmrGroverIteration (-(Real.pi / 2)) (Real.pi / 2) τ
      = -nmrGroverIterationSimplified (Real.pi / 2) (-(Real.pi / 2)) τ := sorry

/-- **Exercise 7.51, `x₀ = 1 = |01⟩`.** Qubit 1 unmarked (`s₁ = +π/2`), qubit 2 marked
(`s₂ = −π/2`): the Grover iteration equals its simplified form up to the overall phase `−1`:
`G = −((R̄_x R̄_y)^{⊗2} τ · (R̄_x R̄_y ⊗ R_x R̄_y) τ)`. -/
theorem nmrGroverIteration_markedOne (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    nmrGroverIteration (Real.pi / 2) (-(Real.pi / 2)) τ
      = -nmrGroverIterationSimplified (-(Real.pi / 2)) (Real.pi / 2) τ := sorry

end AxQM.Concrete
