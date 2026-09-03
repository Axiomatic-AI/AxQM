/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringBasisChange

/-!
# Concrete: single-qubit basis change diagonalising an arbitrary Pauli string to all-`Z`

This file generalises the matrix core of Nielsen & Chuang **Exercise 4.51** (the specific
`X ⊗ Y ⊗ Z` reduction) to an **arbitrary** `n`-qubit Pauli string, in the setting of
**Problem 4.3(3)** — "implement `exp(-i h_g g Δ)` using `O(n)` one- and two-qubit gates".

## Main results
* `pauliDiagGate a` — the single-qubit basis-change gate for Pauli `σ_a`
  (`![1, H, SH, 1]`: identity for `I`/`Z`, Hadamard for `X`, `S·H` for `Y`).
* `pauliDiagGate_conjTranspose_mul` — each `Bₐ` unitary.
-/

open Matrix Complex

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- The **single-qubit basis-change gate** `Bₐ` diagonalising Pauli `σ_a` to `Z`: `![1, H, SH, 1]`,
i.e. the identity for `I` (`a = 0`) and `Z` (`a = 3`), Hadamard `H` for `X` (`a = 1`), and the `Y`
basis change `S·H` (`basisChangeY`) for `Y` (`a = 2`). -/
noncomputable def pauliDiagGate : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, hadamardC, basisChangeY, 1]

/-- Each diagonalising gate `Bₐ` is unitary: `Bₐ† · Bₐ = 1`. -/
theorem pauliDiagGate_conjTranspose_mul (a : Fin 4) :
    (pauliDiagGate a)ᴴ * pauliDiagGate a = 1 := by
  fin_cases a
  · simp [pauliDiagGate]
  · simpa [pauliDiagGate, hadamardC_isHermitian.eq] using hadamardC_mul_self
  · simpa [pauliDiagGate] using basisChangeY_conjTranspose_mul
  · simp [pauliDiagGate]

/-- Each diagonalising gate `Bₐ` lies in the unitary group `U(2)`. -/
theorem pauliDiagGate_mem_unitaryGroup (a : Fin 4) :
    pauliDiagGate a ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Matrix.mem_unitaryGroup_iff'.2 <| by
    rw [Matrix.star_eq_conjTranspose]; exact pauliDiagGate_conjTranspose_mul a

end AxQM.Concrete
