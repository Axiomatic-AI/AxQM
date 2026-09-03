/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Concrete: the encoding-carried permutation gate `permGate`

The `n`-qubit universality argument (Nielsen & Chuang §4.3/§4.5.2) realises a two-level unitary as a
circuit whose backbone is a family of **classical reversible gates** — the multiply-controlled
`NOT`, the single-wire `NOT`, the basis transpositions of the Gray-code walk, `CNOT`, `Toffoli`.
Each of these acts on the computational basis `|enc x⟩` (`enc : (Fin m → Fin 2) ≃ Fin d` an encoding
of the `m`-bit strings as the `d`-dimensional register) by a *permutation of the bit-strings*
`σ : Equiv.Perm (Fin m → Fin 2)`: `|enc x⟩ ↦ |enc (σ x)⟩`. This file provides the matrix realising
that action, `permGate enc σ`.
-/

open Matrix

namespace AxQM.Concrete

variable {m d : ℕ}

/-- **The encoding-carried permutation gate.** For an encoding `enc : (Fin m → Fin 2) ≃ Fin d` of
the `m`-bit strings as the `d`-dimensional register and a permutation `σ` of the bit-strings,
`permGate enc σ` is Mathlib's permutation matrix of the conjugated permutation `(enc.permCongr σ)⁻¹`
of `Fin d`: the `d × d` matrix sending the basis state `|enc x⟩` to `|enc (σ x)⟩`. It is the matrix
realising a classical reversible gate (`NOT`, `CNOT`, `Toffoli`, multiply-controlled `NOT`, basis
transposition) whose action on bit-strings is `σ`. -/
def permGate (enc : (Fin m → Fin 2) ≃ Fin d) (σ : Equiv.Perm (Fin m → Fin 2)) :
    Matrix (Fin d) (Fin d) ℂ :=
  (enc.permCongr σ)⁻¹.permMatrix ℂ

/-- **Every permutation gate is unitary.** -/
theorem permGate_mem_unitaryGroup (enc : (Fin m → Fin 2) ≃ Fin d)
    (σ : Equiv.Perm (Fin m → Fin 2)) :
    permGate enc σ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  simp only [permGate]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

end AxQM.Concrete
