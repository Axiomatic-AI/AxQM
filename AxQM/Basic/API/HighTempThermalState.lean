/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BlochState
import AxQM.Basic.API.Qudit
import AxQM.Concrete.NmrThermalTwoSpin
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# AxQM.Basic.API — the high-temperature thermal (Gibbs) state

The operator-level form of the high-temperature thermal-equilibrium state of Nielsen & Chuang
§7.7.1 (NMR), together with the single-spin instantiation of Exercise 7.36.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

/-- The **high-temperature thermal (Gibbs) state** `2^{−n}(I − βH) = (1/d)(I − βH)` of a system `S`
with Hamiltonian `H` at inverse temperature `β = 1/(k_B T)` (Nielsen & Chuang eq. 7.140, the
high-temperature / first-order truncation of the exact Gibbs state `e^{−βH}/Z` of eq. 7.139). Here
`d = dim S`, so for an `n`-qubit register `1/d = 2^{−n}`. It is a genuine `State` only in the
high-temperature regime where the operator `(1/d)(I − βH)` is positive, supplied as the hypothesis
`h`; for a traceless `H` (as for the NMR Zeeman Hamiltonians) its trace is automatically one. -/
def highTempThermalState {S : QSystem} (β : ℝ) (H : Observable S)
    (h : ((Module.finrank ℂ S.space : ℂ)⁻¹ • (1 - (β : ℂ) • H.op)).IsDensityOp) : State S where
  op := (Module.finrank ℂ S.space : ℂ)⁻¹ • (1 - (β : ℂ) • H.op)
  isDensity := h

/-- The **single-spin NMR (Zeeman) Hamiltonian** `H = ℏω Z` on the qubit (Nielsen & Chuang §7.7.1),
as the Pauli vector observable `ℏω · (0,0,1)·σ = ℏω Z`. Here `ω` is the precession (Larmor)
frequency and `ℏ` Planck's constant. -/
def nmrHamiltonianSpinOne (ℏ ω : ℝ) : Observable qubit := pauliObservable ![0, 0, ℏ * ω]

/-- **Operator identity behind Exercise 7.36 (`n = 1`).** The single-spin high-temperature thermal
operator `(1/2)(I − β · ℏω Z)` equals `Matrix.toEuclideanCLM (blochMatrix (0, 0, −βℏω))`: the `n
= 1` thermal state is the Bloch state with Bloch vector `(0, 0, −βℏω)`, i.e. `½(I − βℏω Z)` (the
matrix form `1 − (ℏω/2k_BT) Z` of N&C eq. 7.141, with the identity part written as the Bloch
centre). -/
theorem highTempThermalStateSpinOne_op (β ℏ ω : ℝ) :
    (Module.finrank ℂ qubit.space : ℂ)⁻¹ •
        ((1 : qubit.space →L[ℂ] qubit.space) - (β : ℂ) • (nmrHamiltonianSpinOne ℏ ω).op)
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          (Concrete.blochMatrix ![0, 0, -(β * ℏ * ω)]) := by
  have hop : (nmrHamiltonianSpinOne ℏ ω).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.pauliDot ![0, 0, ℏ * ω]) := by
    simp only [nmrHamiltonianSpinOne, pauliObservable_op]
  -- The underlying matrix identity `½(I − β·(0,0,ℏω)·σ) = blochMatrix (0,0,−βℏω)` (N&C eq. 7.141),
  -- proved entrywise.
  have hm : (Module.finrank ℂ qubit.space : ℂ)⁻¹ •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) - (β : ℂ) • Concrete.pauliDot ![0, 0, ℏ * ω])
      = Concrete.blochMatrix ![0, 0, -(β * ℏ * ω)] := by
    rw [finrank_qubit_space, Concrete.blochMatrix, Concrete.pauliDot, Concrete.pauliDot]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Concrete.pauliX, Concrete.pauliY, Concrete.pauliZ,
        Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] <;> ring
  rw [hop, ← hm, map_smul, map_sub, map_one, map_smul]
  rfl

/-- The single-spin Bloch vector `(0, 0, −βℏω)` lies in the closed Bloch ball `‖r‖² ≤ 1` whenever
`(βℏω)² ≤ 1` — the single-spin high-temperature (positivity) condition. -/
theorem nmrThermalStateSpinOne_bloch_ball (β ℏ ω : ℝ) (hr : (β * ℏ * ω) ^ 2 ≤ 1) :
    (![0, 0, -(β * ℏ * ω)] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, -(β * ℏ * ω)] : Fin 3 → ℝ) 1 ^ 2
      + (![0, 0, -(β * ℏ * ω)] : Fin 3 → ℝ) 2 ^ 2 ≤ 1 := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  nlinarith [hr]

/-- **The single-spin high-temperature thermal operator is a density operator** (N&C Exercise 7.36,
`n = 1`), whenever `(βℏω)² ≤ 1` — the single-spin high-temperature/positivity condition. -/
theorem highTempThermalStateSpinOne_isDensity (β ℏ ω : ℝ) (hr : (β * ℏ * ω) ^ 2 ≤ 1) :
    ((Module.finrank ℂ qubit.space : ℂ)⁻¹ •
        ((1 : qubit.space →L[ℂ] qubit.space)
          - (β : ℂ) • (nmrHamiltonianSpinOne ℏ ω).op)).IsDensityOp := by
  rw [highTempThermalStateSpinOne_op]
  exact (blochState ![0, 0, -(β * ℏ * ω)] (nmrThermalStateSpinOne_bloch_ball β ℏ ω hr)).isDensity

/-- The **two-spin NMR (Zeeman) Hamiltonian** `H = ℏ(ω_A Z₁ + ω_B Z₂)` on the `4`-level register
`qudit 4` (Nielsen & Chuang §7.7.1), as the observable with operator
`Matrix.toEuclideanCLM (Concrete.nmrZeemanTwoSpinMatrix ℏ ω_A ω_B)`. Here `ω_A, ω_B` are the two
precession frequencies. -/
def nmrHamiltonianSpinTwo (ℏ ωA ωB : ℝ) : Observable (qudit 4) where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 4) (Concrete.nmrZeemanTwoSpinMatrix ℏ ωA ωB)
  selfAdjoint :=
    (Concrete.nmrZeemanTwoSpinMatrix_isHermitian ℏ ωA ωB).isSelfAdjoint.map
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 4))

/-- The underlying operator of `nmrHamiltonianSpinTwo ℏ ω_A ω_B` is
`Matrix.toEuclideanCLM (Concrete.nmrZeemanTwoSpinMatrix ℏ ω_A ω_B)`. -/
@[simp]
theorem nmrHamiltonianSpinTwo_op (ℏ ωA ωB : ℝ) :
    (nmrHamiltonianSpinTwo ℏ ωA ωB).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 4) (Concrete.nmrZeemanTwoSpinMatrix ℏ ωA ωB) :=
  rfl

/-- **The two-spin `n = 2` thermal-equilibrium state of Nielsen & Chuang eq. 7.142** (resonance case
`ω_A = 4ω_B`): the diagonal density operator `¼(I − βℏω_B·diag(5,3,−3,−5))` of `qudit 4`, whose
computational-basis populations are `Concrete.nmrThermalPopTwoSpin β ℏ ω_B`. -/
def nmrThermalStateSpinTwo (β ℏ ωB : ℝ) (h : (5 * (β * ℏ * ωB)) ^ 2 ≤ 1) : State (qudit 4) where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 4)
          (Matrix.diagonal (fun i => ((Concrete.nmrThermalPopTwoSpin β ℏ ωB i : ℝ) : ℂ)))
  isDensity := by
    rw [ContinuousLinearMap.isDensityOp_iff]
    refine ⟨(Matrix.isPositive_toEuclideanCLM_iff _).mpr ?_, ?_⟩
    · rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact_mod_cast Concrete.nmrThermalPopTwoSpin_nonneg β ℏ ωB h i
    · exact (Matrix.trace_toEuclideanCLM _).trans
        ((Matrix.trace_diagonal _).trans (Concrete.nmrThermalPopTwoSpin_sum β ℏ ωB))

/-- **Operator identity behind Exercise 7.36 (`n = 2`, eq. 7.142).** In the resonance case `ω_A =
4ω_B`, the two-spin high-temperature thermal operator `2⁻²(I − βH) = ¼(I − βH)` equals the
diagonal density matrix `¼(I − βℏω_B·diag(5,3,−3,−5))` = `Matrix.toEuclideanCLM (diag
Concrete.nmrThermalPopTwoSpin)`. -/
theorem highTempThermalStateSpinTwo_op (β ℏ ωB : ℝ) :
    (Module.finrank ℂ (qudit 4).space : ℂ)⁻¹ •
        ((1 : (qudit 4).space →L[ℂ] (qudit 4).space)
          - (β : ℂ) • (nmrHamiltonianSpinTwo ℏ (4 * ωB) ωB).op)
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 4)
          (Matrix.diagonal (fun i => ((Concrete.nmrThermalPopTwoSpin β ℏ ωB i : ℝ) : ℂ))) := by
  rw [nmrHamiltonianSpinTwo_op, finrank_qudit, ← Concrete.nmrHighTempTwoSpinMatrix_eq,
    map_smul, map_sub, map_one, map_smul]
  rfl

/-- **The two-spin high-temperature thermal operator is a density operator** (Nielsen & Chuang,
Exercise 7.36, `n = 2`), in the resonance case `ω_A = 4ω_B` and whenever `(5βℏω_B)² ≤ 1` — the
two-spin high-temperature/positivity condition. -/
theorem highTempThermalStateSpinTwo_isDensity (β ℏ ωB : ℝ) (h : (5 * (β * ℏ * ωB)) ^ 2 ≤ 1) :
    ((Module.finrank ℂ (qudit 4).space : ℂ)⁻¹ •
        ((1 : (qudit 4).space →L[ℂ] (qudit 4).space)
          - (β : ℂ) • (nmrHamiltonianSpinTwo ℏ (4 * ωB) ωB).op)).IsDensityOp := by
  rw [highTempThermalStateSpinTwo_op]
  exact (nmrThermalStateSpinTwo β ℏ ωB h).isDensity

end AxQM
