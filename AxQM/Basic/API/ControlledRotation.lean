/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.HadamardABC
import AxQM.Basic.API.HadamardRotation
import AxQM.Concrete.RotationDecompositionXY

/-!
# AxQM.Basic.API — gate-level rotation algebra for controlled rotations

Gate-level lifts of the single-qubit rotation identities, used to assemble
the controlled rotation gates of Nielsen & Chuang §4.3. Each lemma promotes a matrix
identity to the corresponding `Evolution qubit` gate through the `⋆`-algebra
isomorphism `Matrix.toEuclideanCLM` (multiplicative and sending `1 ↦ 1`), so the reasoning about
controlled rotations can stay entirely at the gate level.
-/

noncomputable section

namespace AxQM

/-- **`R_y(0)` is the identity gate.** -/
theorem rotYGate_zero : rotYGate 0 = Evolution.id := by
  apply Evolution.ext
  rw [rotYGate_op, Concrete.rotY_zero, map_one]
  rfl

/-- **Conjugating `R_y(θ)` by `X` negates its angle:** `X · R_y(θ) · X = R_y(-θ)` at the gate
level. -/
theorem pauliXGate_comp_rotYGate_comp_pauliXGate (θ : ℝ) :
    pauliXGate.comp ((rotYGate θ).comp pauliXGate) = rotYGate (-θ) := by
  apply Evolution.ext
  simp only [Evolution.comp_op, pauliXGate_op, rotYGate_op]
  rw [← Concrete.pauliX_mul_rotY_mul_pauliX θ, map_mul, map_mul, mul_assoc]
  rfl

end AxQM
