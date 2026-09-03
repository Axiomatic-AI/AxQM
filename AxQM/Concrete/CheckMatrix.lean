/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCommutation
import Mathlib.Data.ZMod.Basic

/-!
# Concrete: the Pauli product law and the check-matrix row of a Pauli string

The algebraic core of Nielsen & Chuang's **check-matrix representation** of the Pauli group
(N&C §10.5.1, the paragraph preceding eq. (10.83) and the proof of Proposition 10.3). The check
matrix records, for a Pauli operator `g`, its `2n`-bit **row** `r(g) = (x_g | z_g)` — a `1` in the
`k`-th `X`-slot when `g` has an `X` (or `Y`) on qubit `k`, a `1` in the `k`-th `Z`-slot when `g`
has a `Z` (or `Y`).

## Main results
* `pauliMul` / `pauliMulPhase` — the Pauli-index product table and its phase table.
* `pauli_mul_eq_smul_pauliMul` — the single-qubit product law `σ_a σ_b = ζ(a,b) σ_{a⊙b}`.
* `pauliMulIndex` / `pauliString_mul_eq_smul` — the `n`-qubit product law `P_g P_h = (∏_k ζ(g_k,
  h_k)) · P_{g ⊙ h}`.
* `pauliBit` / `checkRow` — the single-qubit `(x, z)` bit pair and the `n`-qubit check-matrix row
  `r(g) = (x_g | z_g) : (Fin n → ZMod 2) × (Fin n → ZMod 2)`.
-/

open Matrix Complex

open scoped BigOperators

namespace AxQM.Concrete

/-- The **Pauli-index product** `a ⊙ b`: the index of the Pauli matrix `σ_a σ_b` up to phase. It is
the bitwise XOR of the `(x, z)` bit representations `I = (0,0)`, `X = (1,0)`, `Y = (1,1)`,
`Z = (0,1)` (e.g. `X ⊙ Y = Z`, `Y ⊙ Z = X`). -/
def pauliMul : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

/-- The **phase** `ζ(a, b)` in the single-qubit product `σ_a σ_b = ζ(a,b) σ_{a⊙b}`, a fourth root of
unity: `1` when the two Paulis commute in the naive sense (equal, or one is `I`), `±i` otherwise
(e.g. `X Y = i Z`, `Y X = -i Z`). -/
def pauliMulPhase : Fin 4 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1], ![1, 1, I, -I], ![1, -I, 1, I], ![1, I, -I, 1]]

/-- **Single-qubit Pauli product law**: `σ_a σ_b = ζ(a,b) · σ_{a⊙b}`. Two single-qubit Paulis
multiply to a third up to a fourth-root-of-unity phase; the product index is `pauliMul` and the
phase is `pauliMulPhase`. -/
theorem pauli_mul_eq_smul_pauliMul (a b : Fin 4) :
    pauli a * pauli b = pauliMulPhase a b • pauli (pauliMul a b) := by
  fin_cases a <;> fin_cases b <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [pauliMul, pauliMulPhase, pauli, pauliX, pauliY, pauliZ, Matrix.mul_apply,
        Fin.sum_univ_two])

variable {n : ℕ}

/-- The **`n`-qubit product index** `g ⊙ h`, the componentwise Pauli-index product `k ↦ (g k) ⊙ (h
k)`. -/
def pauliMulIndex (g h : Fin n → Fin 4) : Fin n → Fin 4 := fun k => pauliMul (g k) (h k)

/-- **The `n`-qubit Pauli-string product law**: `P_g P_h = (∏_k ζ(g_k, h_k)) · P_{g ⊙ h}`. The
product of two Pauli strings is a phase times the Pauli string of the product index. This is the
closure fact behind the Pauli group. -/
theorem pauliString_mul_eq_smul (g h : Fin n → Fin 4) :
    pauliString g * pauliString h =
      (∏ k, pauliMulPhase (g k) (h k)) • pauliString (pauliMulIndex g h) := by
  rw [pauliString_eq_kronFamily g, pauliString_eq_kronFamily h, kronFamily_mul]
  simp only [pauli_mul_eq_smul_pauliMul]
  rw [kronFamily_smul_family, pauliString_eq_kronFamily]
  rfl

/-- The **single-qubit check bits** `(x_a, z_a)` of a Pauli index: `I = (0,0)`, `X = (1,0)`, `Y =
(1,1)`, `Z = (0,1)`. -/
def pauliBit : Fin 4 → ZMod 2 × ZMod 2 := fun a => ((pauliXBit a : ZMod 2), (pauliZBit a : ZMod 2))

/-- The **`n`-qubit check-matrix row** `r(g) = (x_g | z_g)` of a Pauli string, its `X`-part and
`Z`-part over `ZMod 2`: `x_g k`, `z_g k` are the check bits of the `k`-th single-qubit Pauli `g k`.
This is the `2n`-bit row that Nielsen & Chuang assigns to a stabilizer generator; the family of rows
of a generating set is the check matrix. -/
def checkRow (g : Fin n → Fin 4) : (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  (fun k => (pauliBit (g k)).1, fun k => (pauliBit (g k)).2)

end AxQM.Concrete
