/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.AxisAngleRotation
import AxQM.Basic.API.HadamardGate
import AxQM.Concrete.AxisAngleGateValues

/-!
# AxQM.Basic.API — Exercise 4.8(2,3): the axis-angle values for `H` and `S`

The content of parts 2 and 3 of Nielsen & Chuang, Exercise 4.8: the operator-level
identities pinning the axis-angle parameters `α, θ, n̂` in `U = e^{iα} R_n̂(θ)` (eq. 4.9) for the
Hadamard gate `H` and the phase gate `S = diag(1, i)`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **phase gate** `S = diag(1, i)` as a closed-system evolution of the `qubit` (Nielsen &
Chuang, §4.2). -/
def sGate : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.sMatrix
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) Concrete.sMatrix_mem_unitaryGroup

/-- **Nielsen & Chuang, Exercise 4.8(2) at the operator level.** The Hadamard gate is `e^{iπ/2}`
times the axis rotation by `θ = π` about `n̂ = (1/√2, 0, 1/√2)`:
`H = e^{iπ/2} • R_{(1/√2, 0, 1/√2)}(π)` (`α = π/2`, `θ = π`). -/
theorem hadamardGate_op_eq_expPiDivTwo_smul_rotAxisGate :
    hadamardGate.op = Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) •
      (rotAxisGate ![(Real.sqrt 2)⁻¹, 0, (Real.sqrt 2)⁻¹] Real.pi).op := sorry

/-- **Nielsen & Chuang, Exercise 4.8(3) at the operator level.** The phase gate `S = diag(1, i)` is
`e^{iπ/4}` times the `ẑ`-axis rotation by `θ = π/2`: `S = e^{iπ/4} • R_z(π/2)` (`α = π/4`,
`θ = π/2`, `n̂ = ẑ`). -/
theorem sGate_op_eq_expPiDivFour_smul_rotZGate :
    sGate.op = Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) • (rotZGate (Real.pi / 2)).op := sorry

end AxQM
