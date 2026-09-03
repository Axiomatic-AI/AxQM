/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PiEighthConjugation
import AxQM.Concrete.AxisAngleGateValues
import AxQM.Concrete.Hadamard
import AxQM.Concrete.Sqrt2IntegerMatrix
import AxQM.Concrete.PauliOuterProduct

/-!
# Concrete: the algebra behind the fault-tolerant π/8-gate circuit (Nielsen & Chuang, Ex. 10.66)

Nielsen & Chuang **Exercise 10.66** ("Fault-tolerant π/8 gate construction", p. 487) asks to
*derive* the circuit of Figure 10.25 — a measurement-based gadget implementing the `T = π/8` gate —
starting from the trivial circuit that swaps `|ψ⟩` into a known `|0⟩` and then applies `T`, and
pushing the final `T` leftward through the swap gadget using two commutation relations. This file
proves the `2 × 2` / `4 × 4` complex-matrix **algebra** those two relations encode, together
with the resulting circuit's correctness.
-/

open Matrix Complex

noncomputable section

namespace AxQM.Concrete

/-- `e^{-iπ/4} = (1 - i)/√2`, in the `-(π/4 : ℝ) * I` argument form used throughout the π/8-gate
circuit relations below. -/
theorem exp_neg_pi_div_four_mul_I_ofReal :
    Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) = invSqrt2 - invSqrt2 * Complex.I := by
  rw [← exp_neg_pi_div_four_mul_I]; congr 1; push_cast; ring

/-- The single-qubit gate `SX = S · X = !![0, 1; i, 0]` (Nielsen & Chuang, eq. 10.120): the phase
gate `S = diag(1, i)` composed with the bit-flip `X`. -/
def sxMatrix : Matrix (Fin 2) (Fin 2) ℂ := sMatrix * pauliX

/-- `SX = !![0, 1; i, 0]` as an explicit matrix. -/
theorem sxMatrix_eq : sxMatrix = !![0, 1; Complex.I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sxMatrix, sMatrix, pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The π/8 gate conjugates `X` to `exp(−iπ/4) SX`** (Nielsen & Chuang, main text p. 486, `TXT† =
e^{−iπ/4}SX`): `T X T† = exp(−iπ/4) • SX`. This is the *correct* form of the relation Exercise
10.66 prints as "`TX = exp(−iπ/4)SX`". -/
theorem tMatrix_conj_pauliX_eq_expNeg_smul_sxMatrix :
    tMatrix * pauliX * tMatrixᴴ = Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) • sxMatrix := sorry

/-- **The printed relation of Exercise 10.66 is false.** As a bare matrix product,
`T X ≠ exp(−iπ/4) SX`. -/
theorem tMatrix_mul_pauliX_ne_expNeg_smul_sxMatrix :
    tMatrix * pauliX ≠ Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) • sxMatrix := sorry

/-- `T` acting on the **control** qubit of a two-qubit register. Since `I` acts trivially and `T =
diag(1, e^{iπ/4})`, this is the diagonal matrix `diag(1, 1, e^{iπ/4}, e^{iπ/4})` — the diagonal
entry on index `k` is `T` evaluated on the control bit of `k`. -/
def tCtrl : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, 1, tMatrix 1 1, tMatrix 1 1]

/-- **The relation `TU = UT`** of Exercise 10.66 (`U` = CNOT, `T` on the control): `T ⊗ I` commutes
with the CNOT, `tCtrl · CNOT = CNOT · tCtrl`. -/
theorem tCtrl_mul_cnotMatrix_comm : tCtrl * cnotMatrix = cnotMatrix * tCtrl := sorry

/-- The nontrivial diagonal entry `T₁₁ = e^{iπ/4}` **squares to `i`**: `T₁₁ · T₁₁ = i`. -/
theorem tMatrix_apply_one_one_mul_self : tMatrix 1 1 * tMatrix 1 1 = Complex.I := by
  rw [tMatrix_apply_one_one]
  have hexpand : (invSqrt2 + invSqrt2 * Complex.I) * (invSqrt2 + invSqrt2 * Complex.I)
      = invSqrt2 * invSqrt2 * (1 + Complex.I * Complex.I)
        + invSqrt2 * invSqrt2 * 2 * Complex.I := by ring
  rw [hexpand, invSqrt2_mul_self, Complex.I_mul_I]; ring

/-- The ancilla state `|Θ⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2` of Fig. 10.25 (Nielsen & Chuang, eq. 10.118),
as a column vector `Fin 2 → ℂ`; here `T₁₁ = e^{iπ/4}` is the nontrivial diagonal entry of `T`. It
is the `+1` eigenstate of `e^{−iπ/4}SX` that the fault-tolerant π/8 gate consumes. -/
def thetaVec : Fin 2 → ℂ := ![invSqrt2, invSqrt2 * tMatrix 1 1]

/-- **The moved-left `T` reconstructs the Fig. 10.25 ancilla**. -/
theorem tMatrix_mulVec_hadamardC_mulVec_ket_zero :
    tMatrix *ᵥ (hadamardC *ᵥ ket 0) = thetaVec := sorry

/-- The big-endian tensor product `u ⊗ v` of two single-qubit column vectors, as a `Fin 4 → ℂ`
vector with index `2i + j ↦ uᵢ vⱼ` (order `00, 01, 10, 11`) — the convention under which
`cnotMatrix` has its first qubit as control. -/
def kron2 (u v : Fin 2 → ℂ) : Fin 4 → ℂ := ![u 0 * v 0, u 0 * v 1, u 1 * v 0, u 1 * v 1]

/-- The two-qubit state **after the Fig. 10.25 controlled-NOT** (Nielsen & Chuang, eq. 10.119),
`CNOT (|Θ⟩ ⊗ |ψ⟩)`, with the ancilla `|Θ⟩` as control (first qubit) and the data `|ψ⟩ = a|0⟩ +
b|1⟩` as target (second qubit). -/
def piEighthCircuitOut (a b : ℂ) : Fin 4 → ℂ := cnotMatrix *ᵥ kron2 thetaVec ![a, b]

/-- **Fig. 10.25, measurement outcome `0`.** When the data qubit is measured `0`, the (unnormalised)
ancilla-wire component is `(1/√2) • T|ψ⟩` — already the π/8-rotated state, so no correction is
needed. The ancilla amplitudes for data `= 0` sit at indices `0, 2` of `piEighthCircuitOut`. -/
theorem piEighthCircuitOut_measure_zero (a b : ℂ) :
    ![piEighthCircuitOut a b 0, piEighthCircuitOut a b 2] = invSqrt2 • (tMatrix *ᵥ ![a, b]) := sorry

/-- **Fig. 10.25, measurement outcome `1`.** When the data qubit is measured `1`, applying the
classically-controlled correction `SX` to the ancilla-wire component gives `(e^{iπ/4}/√2) • T|ψ⟩` —
the π/8-rotated state up to the nonzero scalar `e^{iπ/4}/√2`, which differs from outcome `0`'s
scalar `1/√2` only by the physically-irrelevant global phase `e^{iπ/4}` (so both branches leave the
ancilla wire in the *same physical state* `T|ψ⟩`). The ancilla amplitudes for data `= 1` sit at
indices `1, 3` of `piEighthCircuitOut`. -/
theorem piEighthCircuitOut_measure_one (a b : ℂ) :
    sxMatrix *ᵥ ![piEighthCircuitOut a b 1, piEighthCircuitOut a b 3]
      = (invSqrt2 * tMatrix 1 1) • (tMatrix *ᵥ ![a, b]) := sorry

end AxQM.Concrete
