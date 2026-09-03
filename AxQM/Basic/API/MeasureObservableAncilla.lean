/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EigenspaceCollapse
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.ControlMeasurementCommute
import AxQM.Basic.API.MeasurementOperation

/-!
# AxQM.Basic.API — the ancilla measurement of the Hadamard-controlled-`U` circuit

The step Nielsen & Chuang's **Exercise 4.34** ("Measuring an operator") asks for, beyond the
circuit-action statement:
*running the ancilla measurement as an explicit `Measurement`* and showing it reproduces the
projective measurement of the observable `U`.  The circuit
`measureObservableCircuit U = (H ⊗ 1)·C(U)·(H ⊗ 1)` sends `|0⟩ ⊗ |ψ⟩` to the correlated state
`|0⟩ ⊗ P₊|ψ⟩ + |1⟩ ⊗ P₋|ψ⟩`; here we *measure the ancilla in the computational basis* — the
primitive `controlMeasurement`, `Mᵢ = |i⟩⟨i| ⊗ 1` — and prove that outcome `i ∈ {0, 1}` occurs with
exactly the Born probability of the sign measurement of `U` and collapses the target onto the
corresponding `±1` eigenvector.

## Main declarations
* `measureObservableCircuit_controlMeasurement_bornProb` — **the statistics of `U`.** Measuring the
  ancilla after the circuit gives outcome `i` with exactly the Born probability of the projective
  sign measurement `Observable.signMeasurement` of `U`: `controlMeasurement.bornProb (circuit|0⟩⊗ψ)
  i = (signMeasurement U).bornProb ψ i`. This is the precise sense in which reading the ancilla *is*
  the measurement of the observable `U`.
* `measureObservableCircuit_controlMeasurement_postMeasurement_zero` / `…_postMeasurement_one` —
  **the post-measurement states of `U`.** Outcome `0` collapses the joint state to `|0⟩ ⊗
  postMeasPlus`, outcome `1` to `|1⟩ ⊗ postMeasMinus`; by `Observable.postMeasPlus_hasEigenstate` /
  `postMeasMinus_hasEigenstate` these targets are genuine `+1` / `−1` eigenvectors of `U`. This is
  the exercise's post-measurement state, the corresponding eigenvector.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The statistics of the observable `U`.**  Measuring the ancilla of the Hadamard-controlled-`U`
circuit in the computational basis, on input `|0⟩ ⊗ |ψ⟩`, gives outcome `i ∈ {0, 1}` with
exactly the Born probability of the projective sign measurement `Observable.signMeasurement` of
`U`: `controlMeasurement.bornProb (circuit |0⟩⊗ψ) i = (signMeasurement U).bornProb ψ i`.
-/
theorem measureObservableCircuit_controlMeasurement_bornProb (U : Evolution S)
    (hsa : IsSelfAdjoint U.op) (ψ : PureState S) (i : Fin 2) :
    (controlMeasurement S).bornProb
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0).tmul ψ)).toState i
      = ((U.toObservable hsa).signMeasurement (U.toObservable_op_mul_self hsa)).bornProb ψ.toState
          i := sorry

/-- **The post-measurement state of `U`, outcome `0` (`+1`).**  Measuring the ancilla of the
Hadamard-controlled-`U` circuit and obtaining outcome `0` collapses the joint state to `|0⟩ ⊗
postMeasPlus`, the corresponding `+1` eigenvector. -/
theorem measureObservableCircuit_controlMeasurement_postMeasurement_zero (U : Evolution S)
    (hsa : IsSelfAdjoint U.op) (ψ : PureState S) (hne : (U.toObservable hsa).projPlus ψ.vec ≠ 0)
    (hp : (controlMeasurement S).bornProb
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0).tmul ψ)).toState 0 ≠ 0) :
    (controlMeasurement S).postMeasurement
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0).tmul ψ)).toState 0 hp
      = ((qubitBasis 0).tmul ((U.toObservable hsa).postMeasPlus ψ hne)).toState := sorry

/-- **The post-measurement state of `U`, outcome `1` (`−1`).**  Measuring the ancilla of the
Hadamard-controlled-`U` circuit and obtaining outcome `1` collapses the joint state to `|1⟩ ⊗
postMeasMinus`, the corresponding `−1` eigenvector. -/
theorem measureObservableCircuit_controlMeasurement_postMeasurement_one (U : Evolution S)
    (hsa : IsSelfAdjoint U.op) (ψ : PureState S) (hne : (U.toObservable hsa).projMinus ψ.vec ≠ 0)
    (hp : (controlMeasurement S).bornProb
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0).tmul ψ)).toState 1 ≠ 0) :
    (controlMeasurement S).postMeasurement
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0).tmul ψ)).toState 1 hp
      = ((qubitBasis 1).tmul ((U.toObservable hsa).postMeasMinus ψ hne)).toState := sorry

end AxQM
