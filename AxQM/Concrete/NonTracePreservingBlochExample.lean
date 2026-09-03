/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochMatrix
import AxQM.Concrete.PauliOuterProduct

/-!
# Concrete: a non-trace-preserving qubit operation with no affine Bloch-sphere picture

This file supplies the mathematical content behind **Nielsen & Chuang, Exercise 8.16 (p. 378)**.
-/

namespace AxQM.Concrete

open Matrix
open scoped ComplexOrder

/-- The computational-basis projector `P₀ = |0⟩⟨0| = !![1, 0; 0, 0]`, the single operation element
of the non-trace-preserving qubit operation of Nielsen & Chuang, Exercise 8.16. This is the shared
`Concrete.ketBra 0 0` of `Concrete.PauliOuterProduct`, reused here rather than
re-spelled as a raw matrix literal; recall `ketBra 0 0 = ½(pauliI + pauliZ)`
(`pauliI_eq_ketBra`/`pauliZ_eq_ketBra`), i.e. `P₀ = ½(I + Z)`. -/
noncomputable def projZero : Matrix (Fin 2) (Fin 2) ℂ := ketBra 0 0

/-- The **quantum operation** `E(ρ) = P₀ ρ P₀†` with the single operation element `P₀ = |0⟩⟨0|`
(`projZero`): the operator-sum representation with one Kraus operator, realising a
computational-basis projective measurement post-selected on the outcome `0`. Non-trace-preserving
(Nielsen & Chuang, Exercise 8.16). -/
noncomputable def projZeroOp (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  projZero * A * projZeroᴴ

/-- **Non-trace-preservation, physical form.** `projZeroOp` does not preserve the trace: there is a
density matrix whose image has a different trace. -/
theorem projZeroOp_not_tracePreserving :
    ¬ ∀ A : Matrix (Fin 2) (Fin 2) ℂ, (projZeroOp A).trace = A.trace := sorry

/-- **Nielsen & Chuang, Exercise 8.16 (the answer).** The non-trace-preserving quantum operation
`E(ρ) = P₀ ρ P₀†` **cannot** be described as an affine map of the Bloch sphere — a deformation `S`,
followed by a rotation `O`, followed by a displacement `c` — i.e. there is **no** real `3 × 3`
matrix `M` and vector `c` with `E(ρ_r) = ρ_{M r + c}` for all Bloch vectors `r` of physical states
(`‖r‖² ≤ 1`). (Since every real `M` factors as `M = O S` by polar decomposition, ranging over all
affine `(M, c)` is exactly ranging over all deformation-rotation-displacement maps.) -/
theorem projZeroOp_not_blochAffine :
    ¬ ∃ (M : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ),
      ∀ r : Fin 3 → ℝ, r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1 →
        projZeroOp (blochMatrix r) = blochMatrix (M *ᵥ r + c) := sorry

end AxQM.Concrete
