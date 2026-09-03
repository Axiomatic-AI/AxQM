/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationDecompositionXY
import AxQM.ToMathlib.NumberTheory.CosThreeFifthsIrrational
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Concrete: the Deutsch gate's target operation `iR_x(θ)`

The target operation `iR_x(θ)` of the Deutsch gate of Nielsen & Chuang, Exercise 4.44, and its
unitarity.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The **target operation of the Deutsch gate** `iR_x(θ) = i · R_x(θ)` as a raw `2 × 2` matrix.
The doubly-controlled application of this operation to the target qubit is the Deutsch gate `G`. -/
noncomputable def iRxMat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • rotX θ

/-- **The Deutsch target `iRxMat θ = i · R_x(θ)` is unitary.** -/
theorem iRxMat_mem_unitaryGroup (θ : ℝ) : iRxMat θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, iRxMat, star_smul, smul_mul_smul_comm,
    Matrix.mem_unitaryGroup_iff.mp (rotX_mem_unitaryGroup θ),
    show Complex.I * star Complex.I = 1 by simp [Complex.I_mul_I], one_smul]

end AxQM.Concrete
