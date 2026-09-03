/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BlochRotationGate
import AxQM.Concrete.Rotation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# AxQM.Basic.API — Exercise 4.8(1): every single-qubit gate is a phase × `R_n̂(θ)`

The content of the first part of Nielsen & Chuang, Exercise 4.8: the operator-level
statement that *every* single-qubit gate is a phase times an axis-rotation gate.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.8(1) at the operator level.** Every single-qubit gate `U :
Evolution qubit` equals a phase times an axis-rotation gate. -/
theorem Evolution.exists_op_eq_phase_smul_rotAxisGate (U : Evolution qubit) :
    ∃ (α θ : ℝ) (n : Fin 3 → ℝ), (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) ∧
      U.op = Complex.exp ((α : ℂ) * Complex.I) • (rotAxisGate n θ).op := sorry

end AxQM
