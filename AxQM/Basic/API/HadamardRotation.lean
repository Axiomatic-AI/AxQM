/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.PiEighthGate
import AxQM.Concrete.Rotation
import AxQM.Concrete.Hadamard

/-!
# AxQM.Basic.API — the Hadamard gate as a product of `R_x`, `R_z` rotation gates

The operator-level content of Nielsen & Chuang, Exercise 4.4: the Hadamard gate `H` equals the
product `R_x(π/2) R_z(π/2) R_x(π/2)` of `x`- and `z`-rotation gates, up to the global phase
`e^{iπ/2}`.

## Main declarations
* `rotXGate θ` — the **`x`-axis rotation gate** `R_x(θ) = exp(-iθX/2)` as an `Evolution qubit`.
* `hadamardGate_op_eq_expPiDivTwo_smul_rotXGate_rotZGate_rotXGate` — **Exercise 4.4 at the operator
  level**: `H = e^{iπ/2} • (R_x(π/2) R_z(π/2) R_x(π/2))` as operators on the qubit state space.
-/

noncomputable section

namespace AxQM

/-- The **`x`-axis rotation gate** `R_x(θ) = exp(-iθX/2)` as a closed-system evolution of the
`qubit` (Nielsen & Chuang, eq. 4.4). -/
def rotXGate (θ : ℝ) : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotX θ)
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) (Concrete.rotX_mem_unitaryGroup θ)

/-- **Nielsen & Chuang, Exercise 4.4 at the operator level.** The Hadamard gate equals the
`X`–`Z`–`X` rotation product up to the global phase `e^{iπ/2}`:
`H = e^{iπ/2} • (R_x(π/2) R_z(π/2) R_x(π/2))`, as operators on the qubit state space. -/
theorem hadamardGate_op_eq_expPiDivTwo_smul_rotXGate_rotZGate_rotXGate :
    hadamardGate.op = Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) •
      (((rotXGate (Real.pi / 2)).comp (rotZGate (Real.pi / 2))).comp
        (rotXGate (Real.pi / 2))).op := sorry

end AxQM
