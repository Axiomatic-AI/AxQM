/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.PiEighthGate
import AxQM.Basic.API.ControlledUnitary
import AxQM.Concrete.HadamardABC

/-!
# AxQM.Basic.API — the ABC decomposition of the Hadamard gate (operator level)

The operator-level content of Nielsen & Chuang, Exercise 4.12: the Hadamard gate `H` equals the ABC
product `A X B X C` (of `y`/`z`-rotation gates and the Pauli-`X` gate) up to the global phase
`e^{iπ/2}`, where the witnesses are those of Corollary 4.2 for the Hadamard's Z–Y parameters.

## Main declarations
* `rotYGate θ` — the **`y`-axis rotation gate** `R_y(θ) = exp(-iθY/2)` as an `Evolution qubit` (the
  `y`-axis analogue of `rotXGate`/`rotZGate`).
* `hadamardGate_op_eq_expPiDivTwo_smul_hadamardABCGate` — **Exercise 4.12 at the operator level**:
  `H = e^{iπ/2} • (A X B X C)` as operators on the qubit state space.
-/

noncomputable section

namespace AxQM

/-- The **`y`-axis rotation gate** `R_y(θ) = exp(-iθY/2)` as a closed-system evolution of the
`qubit` (Nielsen & Chuang, eq. 4.5), the `y`-axis analogue of `rotXGate`/`rotZGate`. -/
def rotYGate (θ : ℝ) : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotY θ)
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) (Concrete.rotY_mem_unitaryGroup θ)

@[simp]
theorem rotYGate_op (θ : ℝ) :
    (rotYGate θ).op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotY θ) := rfl

/-- **Nielsen & Chuang, Exercise 4.12 at the operator level.** The Hadamard gate equals its ABC
product up to the global phase `e^{iπ/2}`. -/
theorem hadamardGate_op_eq_expPiDivTwo_smul_hadamardABCGate :
    hadamardGate.op = Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) •
      (((((rotYGate (Real.pi / 4)).comp pauliXGate).comp
          ((rotYGate (-(Real.pi / 4))).comp (rotZGate (-(Real.pi / 2))))).comp pauliXGate).comp
          (rotZGate (Real.pi / 2))).op := sorry

end AxQM
