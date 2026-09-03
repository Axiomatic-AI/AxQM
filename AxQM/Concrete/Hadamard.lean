/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import AxQM.ToMathlib.LinearAlgebra.Matrix.HermitianUnitary
import Mathlib.Tactic.LinearCombination

/-!
# Concrete: the Hadamard matrix and its `n`-fold tensor (Kronecker) power

It defines the single-qubit
Hadamard matrix `H` and its `n`-fold tensor power `H^{⊗n}` over `ℝ`, proves the closed
entry formula of Nielsen & Chuang, Exercise 2.33 (p. 74), and — for the qubit *operator*
work of Chapter 2 — the complex-entried Hadamard `H` together with its Hermiticity,
involution `H² = I`, and unitarity (membership in `Matrix.unitaryGroup`).

## The exercise

N&C write the one-qubit Hadamard operator (eq. 2.54) as `H = (1/√2) [(|0⟩ + |1⟩)⟨0| + (|0⟩ −
|1⟩)⟨1|]`, i.e. the real `2 × 2` matrix `(1/√2) !![1, 1; 1, -1]`, and ask to show that the Hadamard
transform on `n` qubits `H^{⊗n}` may be written (eq. 2.55) as `H^{⊗n} = (1/√(2ⁿ)) ∑_{x,y} (-1)^{x·y}
|x⟩⟨y|`, where `x, y` range over `n`-bit strings and `x·y = ∑ᵢ xᵢ yᵢ` is the bitwise dot product.
Finally it asks for an explicit matrix for `H^{⊗2}`.

## Main declarations
* `hadamard` — the `2 × 2` real matrix `(√2)⁻¹ • !![1, 1; 1, -1]` of eq. (2.54).
* `hadamardPow n` — the `n`-fold tensor power, indexed by `n`-bit strings `Fin n → Fin 2`,
  defined by the honest block (Kronecker) recursion
  `H^{⊗(n+1)} x y = H (x 0) (y 0) · H^{⊗n} (tail x) (tail y)`.
* `hadamardPow_apply_eq` — **eq. (2.55)**: `H^{⊗n} x y = (√(2ⁿ))⁻¹ (-1)^{∑ᵢ xᵢ yᵢ}`. This is the
  exercise's main claim.
* `hadamardPow_two_submatrix` — the explicit `4 × 4` matrix for `H^{⊗2}`, in N&C's
  big-endian basis order `00, 01, 10, 11` (given by `bitPair2`).
-/

namespace AxQM.Concrete

open Matrix

/-- The single-qubit Hadamard matrix `H = (1/√2) !![1, 1; 1, -1]` (Nielsen & Chuang,
eq. 2.54). Its columns are `(|0⟩ + |1⟩)/√2` and `(|0⟩ − |1⟩)/√2`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt 2)⁻¹ • !![1, 1; 1, -1]

/-- The `n`-fold tensor (Kronecker) power `H^{⊗n}` of the Hadamard matrix, indexed by the
`n`-bit strings `Fin n → Fin 2`. Defined by the block recursion of the Kronecker product:
`H^{⊗0} = I` (a `1 × 1` matrix on the singleton index) and
`H^{⊗(n+1)} x y = H (x 0) (y 0) · H^{⊗n} (tail x) (tail y)`, i.e. the first qubit contributes
the Hadamard factor `H (x 0) (y 0)` and the remaining `n` qubits contribute `H^{⊗n}`. -/
noncomputable def hadamardPow : (n : ℕ) → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℝ
  | 0 => 1
  | n + 1 => fun x y => hadamard (x 0) (y 0) * hadamardPow n (Fin.tail x) (Fin.tail y)

/-- **Nielsen & Chuang, Exercise 2.33 (eq. 2.55).** The Hadamard transform on `n` qubits has the
closed form `H^{⊗n} x y = (√(2ⁿ))⁻¹ (-1)^{x·y}`, where `x·y = ∑ᵢ xᵢ yᵢ` is the bitwise dot
product of the `n`-bit strings `x, y`. -/
theorem hadamardPow_apply_eq (n : ℕ) (x y : Fin n → Fin 2) :
    hadamardPow n x y
      = (Real.sqrt (2 ^ n))⁻¹ * (-1) ^ (∑ i, (x i).val * (y i).val) := sorry

/-- The four `2`-bit strings listed in Nielsen & Chuang's big-endian order `00, 01, 10, 11`
(the first component is the most significant bit). Used to reindex `H^{⊗2}` as an explicit
`4 × 4` matrix. -/
def bitPair2 : Fin 4 → (Fin 2 → Fin 2) := ![![0, 0], ![0, 1], ![1, 0], ![1, 1]]

/-- **Nielsen & Chuang, Exercise 2.33 (explicit `H^{⊗2}`).** In the big-endian basis order
`00, 01, 10, 11` (via `bitPair2`), the two-qubit Hadamard transform is the `4 × 4` matrix
`(1/2) !![1,1,1,1; 1,-1,1,-1; 1,1,-1,-1; 1,-1,-1,1]`. Each entry is `(1/2)(-1)^{x·y}` by the
`n = 2` case of eq. (2.55). -/
theorem hadamardPow_two_submatrix :
    (hadamardPow 2).submatrix bitPair2 bitPair2
      = (2⁻¹ : ℝ) • !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1] := sorry

open Matrix Complex in
/-- The single-qubit Hadamard matrix `H = (1/√2) !![1, 1; 1, -1]` with **complex** entries
(Nielsen & Chuang, eq. 2.85). This is the operator form of `hadamard`, used to build the qubit
Hadamard gate; the two are the same matrix over `ℝ` resp. `ℂ`. -/
noncomputable def hadamardC : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ))⁻¹ • !![1, 1; 1, -1]

/-- The complex Hadamard matrix is Hermitian (`Hᴴ = H`): its entries `±1/√2` are real, and the
matrix is symmetric. -/
theorem hadamardC_isHermitian : hadamardC.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hadamardC, Matrix.conjTranspose_apply]

/-- The Hadamard matrix is an involution: `H² = I`. The scalar `((√2)⁻¹)² = 2⁻¹` combines with
`!![1,1;1,-1]² = 2 • I` to give the identity. (This is also Nielsen & Chuang, Exercise 2.52.) -/
theorem hadamardC_mul_self : hadamardC * hadamardC = 1 := by
  have hc : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ * 2 = 1 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hBB : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; 1, -1]
      = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  rw [hadamardC, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hBB, smul_smul, hc, one_smul]

/-- **Nielsen & Chuang, Exercise 2.51. -/
theorem hadamardC_mem_unitaryGroup : hadamardC ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  hadamardC_isHermitian.mem_unitaryGroup hadamardC_mul_self

end AxQM.Concrete
