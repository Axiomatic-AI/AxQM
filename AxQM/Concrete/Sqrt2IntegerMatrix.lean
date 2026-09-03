/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Hadamard
import AxQM.Concrete.AxisAngleGateValues
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Concrete: circuit matrices over `H, S, CNOT, Toffoli` are `2⁻ᵏ⸍² M` (Gaussian `M`)

The mathematical core of the first half of **Nielsen & Chuang, Exercise 4.45** (p. 198). N&C ask
one to show that a unitary `U`
implemented by an `n`-qubit circuit built from the Hadamard `H`, phase `S`, `CNOT` and Toffoli
gates always has the form `U = 2⁻ᵏ⸍² M` for some integer `k`, where `M` is a `2ⁿ × 2ⁿ` matrix with
*complex integer* (Gaussian-integer, `ℤ[i]`) entries; and to repeat the exercise with the Toffoli
gate replaced by the `π/8` gate `T`.
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

noncomputable section

variable {m n p q m' n' : Type*}

/-- **The `√2`-scaled-integer form.** A complex matrix `U` *is `√2`-scaled over the subring `R ⊆ ℂ`*
when `U = (√2)⁻¹ᵏ • M` for some `k : ℕ` and some matrix `M` with entries in `R`; since
`(√2)⁻¹ᵏ = 2⁻ᵏ⸍²`, this is Nielsen & Chuang's `2⁻ᵏ⸍² M` form with the integer scale `k` shared
across all entries. The gate ring of the `H, S, CNOT, Toffoli` variant of
Exercise 4.45 is `R = ℤ[i]` (`gaussianIntSubring`); the `T` variant uses `R = ℤ[ζ₈]`. -/
def IsSqrt2ScaledIn (R : Subring ℂ) (U : Matrix m n ℂ) : Prop :=
  ∃ (k : ℕ) (M : Matrix m n R), U = ((Real.sqrt 2 : ℂ))⁻¹ ^ k • M.map R.subtype

/-- **The Gaussian integers `ℤ[i] ⊆ ℂ`**, `{a + b·i : a, b ∈ ℤ}` — Nielsen & Chuang's "complex
integers", the entry ring of the `H, S, CNOT, Toffoli` variant of Exercise 4.45. -/
def gaussianIntSubring : Subring ℂ where
  carrier := {z | ∃ a b : ℤ, z = a + b * Complex.I}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩; exact ⟨a + c, b + d, by push_cast; ring⟩
  mul_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - b * d, a * d + b * c, ?_⟩
    push_cast
    linear_combination (b * d : ℂ) * Complex.I_mul_I
  neg_mem' := by rintro x ⟨a, b, rfl⟩; exact ⟨-a, -b, by push_cast; ring⟩

/-- `i ∈ ℤ[i]`. -/
theorem complexI_mem_gaussianIntSubring : Complex.I ∈ gaussianIntSubring := ⟨0, 1, by simp⟩

/-- The **`CNOT` gate matrix** (control = first qubit), the basis permutation swapping `|10⟩ ↔ |11⟩`
(indices `2 ↔ 3` in the big-endian order `00, 01, 10, 11`). -/
def cnotMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => if Equiv.swap 2 3 i = j then 1 else 0

/-- The **Toffoli gate matrix** (controls = first two qubits), the basis permutation swapping
`|110⟩ ↔ |111⟩` (indices `6 ↔ 7` in the big-endian order `000, …, 111`). -/
def toffoliMatrix : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if Equiv.swap 6 7 i = j then 1 else 0

/-- **Nielsen & Chuang, Exercise 4.45 (`H, S, CNOT, Toffoli`).** The unitary of any circuit — the
product `L.prod` of a list `L` of matrices each of which is a `√2`-scaled Gaussian-integer matrix
(e.g. an embedded `H`/`S`/`CNOT`/`Toffoli` gate) — has the form `2⁻ᵏ⸍² M` with `M` a `2ⁿ × 2ⁿ`
Gaussian-integer matrix. -/
theorem exists_circuit_form_gaussian [Fintype m] [DecidableEq m]
    (L : List (Matrix m m ℂ)) (h : ∀ U ∈ L, IsSqrt2ScaledIn gaussianIntSubring U) :
    ∃ (k : ℕ) (M : Matrix m m ℂ),
      (∀ i j, ∃ a b : ℤ, M i j = a + b * Complex.I) ∧
        L.prod = (((2 : ℝ) ^ (-(k : ℝ) / 2) : ℝ) : ℂ) • M := sorry

end

end AxQM.Concrete
