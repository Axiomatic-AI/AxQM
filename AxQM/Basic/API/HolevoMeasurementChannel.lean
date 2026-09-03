/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuantumChannel
import AxQM.Basic.API.PeriodShift
import AxQM.Basic.Composite
import AxQM.Basic.Measurement
import AxQM.ToMathlib.Analysis.InnerProductSpace.Polar
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Basic.API — the Holevo measurement operation `𝓔` (N&C Exercise 12.2)

The underlying operator bridge realizing **Nielsen & Chuang, Exercise 12.2** (p. 533), the
construction used in
the proof of the Holevo bound. The quantum operation `𝓔` there acts on the system `Q`
Alice gives Bob together with Bob's measuring apparatus `M`, performing a measurement with POVM
elements `{E_y}` on `Q` and *storing the outcome* in `M`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {Q : QSystem} {r : ℕ} [NeZero r]

/-- **The operation element `√E_y ⊗ U_y` of outcome `y`** (Nielsen & Chuang, Exercise 12.2), on the
composite of the measured system `Q` and the apparatus `qudit r`. Here `√E_y = |M_y|` is the
positive square root of the POVM effect `E_y = M_y† M_y` of the measurement `m` (the absolute value
of the measurement operator `M_y`), and `U_y = periodShift r y` is the cyclic shift storing the
outcome, `U_y|0⟩ = |y⟩`. -/
def holevoMeasurementKraus (m : Measurement (Fin r) Q) (y : Fin r) :
    (Q ⊗ qudit r).space →L[ℂ] (Q ⊗ qudit r).space :=
  TensorProduct.mapL (m.op y).absoluteValue (periodShift r y).op

/-- **Nielsen & Chuang, Exercise 12.2 (trace preservation).** The operation elements `{√E_y ⊗ U_y}`
obey the completeness relation `∑_y (√E_y ⊗ U_y)† (√E_y ⊗ U_y) = 1`, so they define a
*trace-preserving* quantum operation. Each summand is `(|M_y|† |M_y|) ⊗ (U_y† U_y) = (M_y† M_y) ⊗ 1`
— the square root is self-adjoint with `|M_y|² = E_y` (`absoluteValue_sq`) and `U_y` is unitary —
and `∑_y M_y† M_y = 1` is the measurement's completeness. -/
theorem holevoMeasurementKraus_completeness (m : Measurement (Fin r) Q) :
    ∑ y, (adjoint (holevoMeasurementKraus m y)).comp (holevoMeasurementKraus m y) = 1 := by
  have key : ∀ y : Fin r,
      (adjoint (holevoMeasurementKraus m y)).comp (holevoMeasurementKraus m y)
        = TensorProduct.mapL ((adjoint (m.op y)).comp (m.op y))
            (1 : (qudit r).space →L[ℂ] (qudit r).space) := by
    intro y
    have h := TensorProduct.mapL_adjoint_comp_self (m.op y).absoluteValue (periodShift r y).op
    rw [ContinuousLinearMap.adjoint_absoluteValue, ContinuousLinearMap.absoluteValue_sq,
      (periodShift r y).adjoint_comp_self] at h
    rw [holevoMeasurementKraus]
    exact h
  calc ∑ y, (adjoint (holevoMeasurementKraus m y)).comp (holevoMeasurementKraus m y)
      = ∑ y, TensorProduct.mapL ((adjoint (m.op y)).comp (m.op y))
            (1 : (qudit r).space →L[ℂ] (qudit r).space) :=
        Finset.sum_congr rfl (fun y _ => key y)
    _ = TensorProduct.mapL (∑ y, (adjoint (m.op y)).comp (m.op y)) 1 :=
        (TensorProduct.mapL_sum_left _ _).symm
    _ = TensorProduct.mapL 1 1 := by rw [m.complete]
    _ = 1 := TensorProduct.mapL_one

/-- **The Holevo measurement operation `𝓔`** (Nielsen & Chuang, Exercise 12.2 / Eq. (12.8)), as a
quantum channel `State (Q ⊗ M) → State (Q ⊗ M)`: `ρ ↦ ∑_y (√E_y ⊗ U_y) ρ (√E_y ⊗ U_y)†`, the
operator sum of the operation elements `holevoMeasurementKraus m`. -/
def holevoMeasurementChannel (m : Measurement (Fin r) Q) :
    State (Q ⊗ qudit r) → State (Q ⊗ qudit r) := fun ρ =>
  { op := ContinuousLinearMap.krausSumₗ (holevoMeasurementKraus m) ρ.op
    isDensity := ContinuousLinearMap.isDensityOp_krausSumₗ (holevoMeasurementKraus m)
      (holevoMeasurementKraus_completeness m) ρ.isDensity }

/-- **Nielsen & Chuang, Exercise 12.2 (a trace-preserving quantum operation).** The Holevo
measurement operation `𝓔` is a genuine quantum channel (completely positive and
trace-preserving). -/
theorem holevoMeasurementChannel_isChannel (m : Measurement (Fin r) Q) :
    IsChannel (holevoMeasurementChannel m) := sorry

/-- **Nielsen & Chuang, Exercise 12.2 (agreement with Eq. (12.8)).** On a state of the form `σ ⊗
|0⟩⟨0|` — the system `σ` together with the apparatus in its standard state `|0⟩` — the Holevo
measurement operation acts as

`𝓔(σ ⊗ |0⟩⟨0|) = ∑_y √E_y σ √E_y ⊗ |y⟩⟨y|`,

exactly Eq. (12.8). Here `√E_y = (m.op y).absoluteValue` and `|y⟩⟨y| = (quditBasis
y).toState.op`.
-/
theorem holevoMeasurementChannel_apply_tmul (m : Measurement (Fin r) Q) (σ : State Q) :
    (holevoMeasurementChannel m (σ ⊗ (quditBasis (0 : Fin r)).toState)).op
      = ∑ y, TensorProduct.mapL
          ((m.op y).absoluteValue.comp (σ.op.comp (m.op y).absoluteValue))
          ((quditBasis y).toState.op) := sorry

end AxQM
