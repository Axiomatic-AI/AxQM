/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.NMRCoupledSpinFID
import AxQM.Basic.API.HighTempThermalState
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy

/-!
# AxQM.Basic.API — the coupled two-spin NMR thermal equilibrium state

The **thermal equilibrium state** of the two-spin, `J`-coupled NMR system of Nielsen & Chuang
Exercise 7.37, on the two-qubit system `qubit.compose qubit`, in the high-temperature
approximation of N&C eq. 7.140.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

/-- The two-qubit dimension: `dim (qubit ⊗ qubit) = 4`. -/
theorem finrank_two_qubit : Module.finrank ℂ (qubit.compose qubit).space = 4 := by
  change Module.finrank ℂ (TensorProduct ℂ qubit.space qubit.space) = 4
  rw [Module.finrank_tensorProduct, finrank_qubit_space]

/-- The **two-spin NMR Zeeman Hamiltonian** `H_Z = ℏω(Z₁ + Z₂)` on `qubit.compose qubit`, both spins
precessing at the same Larmor frequency `ω` (as in Nielsen & Chuang Exercise 7.37). Its operator is
`ℏω • (Z₁ + Z₂)`, a real multiple of the sum of the single-spin `Z` observables `Z₁ = Z ⊗ 1`,
`Z₂ = 1 ⊗ Z`. -/
def nmrCoupledPairZeeman (ℏ ω : ℝ) : Observable (qubit.compose qubit) where
  op := ((ℏ * ω : ℝ) : ℂ) •
    ((pauliZObservable.tmul (Observable.id qubit)).op
      + ((Observable.id qubit).tmul pauliZObservable).op)
  selfAdjoint :=
    ((Complex.im_eq_zero_iff_isSelfAdjoint _).mp rfl).smul
      ((pauliZObservable.tmul (Observable.id qubit)).selfAdjoint.add
        ((Observable.id qubit).tmul pauliZObservable).selfAdjoint)

@[simp]
theorem nmrCoupledPairZeeman_op (ℏ ω : ℝ) :
    (nmrCoupledPairZeeman ℏ ω).op
      = ((ℏ * ω : ℝ) : ℂ) •
        ((pauliZObservable.tmul (Observable.id qubit)).op
          + ((Observable.id qubit).tmul pauliZObservable).op) :=
  rfl

/-- `Z₁ = Z ⊗ 1` is a **self-adjoint involution** (`Z₁² = 1`). -/
theorem pauliZ_tmul_one_mul_self :
    (pauliZObservable.tmul (Observable.id qubit)).op
        * (pauliZObservable.tmul (Observable.id qubit)).op = 1 := by
  rw [Observable.tmul_op, Observable.id_op]
  exact ContinuousLinearMap.mapL_mul_mapL_self pauliZObservable_op_mul_self (one_mul 1)

/-- `Z₂ = 1 ⊗ Z` is a **self-adjoint involution** (`Z₂² = 1`). -/
theorem one_tmul_pauliZ_mul_self :
    ((Observable.id qubit).tmul pauliZObservable).op
        * ((Observable.id qubit).tmul pauliZObservable).op = 1 := by
  rw [Observable.tmul_op, Observable.id_op]
  exact ContinuousLinearMap.mapL_mul_mapL_self (one_mul 1) pauliZObservable_op_mul_self

/-- **The high-temperature thermal equilibrium state of the two-spin Zeeman Hamiltonian**
`ρ_th = ¼(I − βℏω(Z₁ + Z₂))` (Nielsen & Chuang eq. 7.140), a genuine `State` on
`qubit.compose qubit` whenever `(2βℏω)² ≤ 1` (the two-spin high-temperature/positivity window,
`‖βℏω(Z₁+Z₂)‖ ≤ 1`). -/
def nmrCoupledPairThermal (β ℏ ω : ℝ) (h : (2 * (β * ℏ * ω)) ^ 2 ≤ 1) :
    State (qubit.compose qubit) :=
  highTempThermalState β (nmrCoupledPairZeeman ℏ ω) <| by
    -- normalise the thermal operator to `¼(I − b(Z₁+Z₂))`, `b = βℏω`
    have hop : (Module.finrank ℂ (qubit.compose qubit).space : ℂ)⁻¹
          • (1 - (β : ℂ) • (nmrCoupledPairZeeman ℏ ω).op)
        = ((4⁻¹ : ℝ) : ℂ) • (1 - ((β * ℏ * ω : ℝ) : ℂ)
            • ((pauliZObservable.tmul (Observable.id qubit)).op
              + ((Observable.id qubit).tmul pauliZObservable).op)) := by
      rw [nmrCoupledPairZeeman_op, finrank_two_qubit, smul_smul]
      push_cast
      module
    rw [hop]
    refine ⟨?_, ?_⟩
    · -- positivity via the ½-split
      have hp1 : (1 - ((2 * (β * ℏ * ω) : ℝ) : ℂ)
            • (pauliZObservable.tmul (Observable.id qubit)).op).IsPositive :=
        ContinuousLinearMap.isPositive_one_sub_smul_of_selfAdjoint_involution
          (pauliZObservable.tmul (Observable.id qubit)).selfAdjoint pauliZ_tmul_one_mul_self h
      have hp2 : (1 - ((2 * (β * ℏ * ω) : ℝ) : ℂ)
            • ((Observable.id qubit).tmul pauliZObservable).op).IsPositive :=
        ContinuousLinearMap.isPositive_one_sub_smul_of_selfAdjoint_involution
          ((Observable.id qubit).tmul pauliZObservable).selfAdjoint one_tmul_pauliZ_mul_self h
      have hsplit : (1 : (qubit.compose qubit).space →L[ℂ] (qubit.compose qubit).space)
            - ((β * ℏ * ω : ℝ) : ℂ) • ((pauliZObservable.tmul (Observable.id qubit)).op
                + ((Observable.id qubit).tmul pauliZObservable).op)
          = ((2⁻¹ : ℝ) : ℂ) • (1 - ((2 * (β * ℏ * ω) : ℝ) : ℂ)
                • (pauliZObservable.tmul (Observable.id qubit)).op)
            + ((2⁻¹ : ℝ) : ℂ) • (1 - ((2 * (β * ℏ * ω) : ℝ) : ℂ)
                • ((Observable.id qubit).tmul pauliZObservable).op) := by
        push_cast
        module
      refine ContinuousLinearMap.IsPositive.smul_of_nonneg ?_
        (Complex.zero_le_real.mpr (by norm_num))
      rw [hsplit]
      exact (hp1.smul_of_nonneg (Complex.zero_le_real.mpr (by norm_num))).add
        (hp2.smul_of_nonneg (Complex.zero_le_real.mpr (by norm_num)))
    · -- unit trace: `Z₁, Z₂` traceless, `tr 1 = 4`
      have htrZ₁ : LinearMap.trace ℂ (qubit.compose qubit).space
          ↑(pauliZObservable.tmul (Observable.id qubit)).op = 0 := by
        rw [Observable.tmul_op, Observable.id_op]
        exact (ContinuousLinearMap.trace_mapL pauliZObservable.op 1).trans (by
          rw [trace_pauliZObservable, zero_mul])
      have htrZ₂ : LinearMap.trace ℂ (qubit.compose qubit).space
          ↑((Observable.id qubit).tmul pauliZObservable).op = 0 := by
        rw [Observable.tmul_op, Observable.id_op]
        exact (ContinuousLinearMap.trace_mapL 1 pauliZObservable.op).trans (by
          rw [trace_pauliZObservable, mul_zero])
      rw [ContinuousLinearMap.coe_smul, map_smul, ContinuousLinearMap.coe_sub, map_sub,
        ContinuousLinearMap.coe_smul, map_smul, ContinuousLinearMap.coe_add, map_add,
        htrZ₁, htrZ₂, add_zero, smul_zero, sub_zero, ContinuousLinearMap.coe_one,
        LinearMap.trace_one, finrank_two_qubit, smul_eq_mul]
      norm_num

/-- The **`Y₁` observable** `Y ⊗ 1` on the first spin, the generator of the read pulse. -/
def nmrPulseGen : Observable (qubit.compose qubit) := pauliYObservable.tmul (Observable.id qubit)

/-- The **`π/2` (`90°`) read pulse** `e^{iπ Y₁/4}` on the first spin (Nielsen & Chuang §7.7.2),
as an `Evolution`: the adjoint of the `Y₁`-propagator `exp(-i Y₁ (π/4)) = e^{-iπ Y₁/4}`. -/
def nmrCoupledPairPulse : Evolution (qubit.compose qubit) :=
  (nmrPulseGen.propagator 1 0 (Real.pi / 4)).adjoint

/-- **The `π/2`-pulsed initial state of Exercise 7.37**, `ρ = e^{iπ Y₁/4} ρ_th e^{−iπ Y₁/4}`, the
two-spin thermal state after the read pulse on the first spin, as a `State`. -/
def nmrCoupledPairPulsedState (β ℏ ω : ℝ) (h : (2 * (β * ℏ * ω)) ^ 2 ≤ 1) :
    State (qubit.compose qubit) :=
  nmrCoupledPairPulse.evolve (nmrCoupledPairThermal β ℏ ω h)

end AxQM
