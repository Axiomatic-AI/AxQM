/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.NMRControlledZ
import AxQM.Basic.API.HadamardRotation
import AxQM.Basic.API.HadamardABC
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# AxQM.Basic.API — machinery for the NMR controlled-`NOT` (N&C Ex 7.47)

The scaffolding for the **controlled-`NOT` circuit of Figure 7.19** (top left): a
`90°` `y`-pulse on the target spin, one period of `Z₁Z₂`-coupled evolution `exp(-i c Z₁Z₂ t)`, then
a `90°` `x`-pulse on the target.

## Main declarations
* `nmrCnotCircuit c t` — the **Fig 7.19 circuit** `R_x(π/2)₂ ∘ exp(-i c Z₁Z₂ t) ∘ R_y(π/2)₂`.
* `nmrCnotPhase a b` — the unit-modulus phase the target picks up at `c·t = π/4`.
* `nmrCnotCircuit_op_apply_phase` — at `c·t = π/4`, `nmrCnotCircuit c t` sends
  `|a⟩⊗|b⟩` to `(nmrCnotPhase a b)·|a⟩⊗|a⊕b⟩`, i.e. it is a controlled-`NOT` up to single-qubit
  phases on classical inputs.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The Fig 7.19 (top left) NMR controlled-`NOT` circuit.** On the target (right) spin: a `90°`
`y`-rotation `R_y(π/2)`, then one period of `Z₁Z₂`-coupled evolution `(couplingZZHamiltonian
c).propagator 1 0 t`, then a `90°` `x`-rotation `R_x(π/2)`. -/
def nmrCnotCircuit (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((rotXGate (Real.pi / 2)).onRight qubit).comp
    (((couplingZZHamiltonian c).propagator 1 0 t).comp
      ((rotYGate (Real.pi / 2)).onRight qubit))

/-- The single-qubit phase picked up by the target in the Fig 7.19 circuit at `c·t = π/4`, one of
the four unit-modulus scalars `e^{-iπ/4}, e^{iπ/4}, e^{-iπ/4}, e^{-3iπ/4}` (given in rectangular
form `(√2/2)(±1 ± i)`). These are exactly the phases that a subsequent single-qubit `R_z` correction
removes to turn the circuit into a proper controlled-`NOT`. -/
def nmrCnotPhase (a b : Fin 2) : ℂ :=
  !![(↑(Real.sqrt 2) / 2 : ℂ) - (↑(Real.sqrt 2) / 2 : ℂ) * Complex.I,
        (↑(Real.sqrt 2) / 2 : ℂ) + (↑(Real.sqrt 2) / 2 : ℂ) * Complex.I;
      (↑(Real.sqrt 2) / 2 : ℂ) - (↑(Real.sqrt 2) / 2 : ℂ) * Complex.I,
        -(↑(Real.sqrt 2) / 2 : ℂ) - (↑(Real.sqrt 2) / 2 : ℂ) * Complex.I] a b

/-- **The Fig 7.19 circuit acts as a controlled-`NOT` up to single-qubit phases on the computational
basis.** For one coupling period `c·t = π/4`, `nmrCnotCircuit c t` sends `|a⟩⊗|b⟩` to
`(phase)·|a⟩⊗|a⊕b⟩`: the target is flipped exactly when the control is `|1⟩` (as `a + b` is `b` for
`a = 0` and `b ⊕ 1` for `a = 1`), each computational-basis input acquiring the unit-modulus scalar
`nmrCnotPhase a b`. This is the precise sense in which the circuit "acts properly on classical input
states" (N&C Exercise 7.47). -/
theorem nmrCnotCircuit_op_apply_phase (c t : ℝ) (h : c * t = Real.pi / 4) (a b : Fin 2) :
    (nmrCnotCircuit c t).op ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
      = nmrCnotPhase a b • ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis (a + b)).vec) := sorry

end AxQM
