/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliMeasurement
import AxQM.Basic.API.PauliEigen
import AxQM.Basic.API.EigenspaceCollapse
import AxQM.Basic.API.RelativePhase

/-!
# AxQM.Basic.API — the six-state protocol states, bases, and measurement

The infrastructure behind the **six-state** quantum-key-distribution protocol
(Nielsen & Chuang Exercise 12.29, p. 591; Bruß 1998), the three-basis generalization of BB84.
Alice's six encoding states — the eigenstates of the three Pauli observables `X`, `Y`, `Z` — the
three mutually conjugate measurement bases, and Bob's projective measurement in a chosen basis.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The six-state measurement observable for basis index `i`.** Bob measures the Pauli `X`
observable when `i = 0` (the `{|+⟩, |−⟩}` basis), `Y` when `i = 1` (the `{|+i⟩, |−i⟩}` basis), and
`Z` when `i = 2` (the computational basis `{|0⟩, |1⟩}`) — the three mutually conjugate bases of the
protocol. -/
def sixStateObservable (i : Fin 3) : Observable qubit :=
  ![pauliXObservable, pauliYObservable, pauliZObservable] i

@[simp] theorem sixStateObservable_zero : sixStateObservable 0 = pauliXObservable := rfl

@[simp] theorem sixStateObservable_one : sixStateObservable 1 = pauliYObservable := rfl

@[simp] theorem sixStateObservable_two : sixStateObservable 2 = pauliZObservable := rfl

/-- Each six-state basis observable is a self-adjoint **involution**: `(sixStateObservable i)² = 1`.
All of `X² = 1`, `Y² = 1`, `Z² = 1` (`pauli{X,Y,Z}Observable_op_mul_self`), so its projective
measurement is a genuine two-outcome `signMeasurement`. -/
theorem sixStateObservable_op_mul_self (i : Fin 3) :
    (sixStateObservable i).op * (sixStateObservable i).op = 1 := by
  fin_cases i
  · simpa using pauliXObservable_op_mul_self
  · simpa using pauliYObservable_op_mul_self
  · simpa using pauliZObservable_op_mul_self

/-- **Alice's six-state encoding state** of data bit `s` in basis `i`: the `(-1)^s`-eigenstate of
`sixStateObservable i`. For the `X` basis (`i = 0`), `|+⟩` (`s = 0`) and `|−⟩` (`s = 1`); for the
`Y` basis (`i = 1`), `|+i⟩` and `|−i⟩`; for the `Z` basis (`i = 2`), `|0⟩` and `|1⟩`. These are the
six eigenstates of `X`, `Y`, `Z` — the states of Exercise 12.29. -/
def sixStateState (i : Fin 3) (s : Fin 2) : PureState qubit :=
  ![![qubitPlus, qubitMinus], ![qubitPlusI, qubitMinusI], ![qubitKet0, qubitBasis 1]] i s

@[simp] theorem sixStateState_zero_zero : sixStateState 0 0 = qubitPlus := rfl

@[simp] theorem sixStateState_zero_one : sixStateState 0 1 = qubitMinus := rfl

@[simp] theorem sixStateState_one_zero : sixStateState 1 0 = qubitPlusI := rfl

@[simp] theorem sixStateState_one_one : sixStateState 1 1 = qubitMinusI := rfl

@[simp] theorem sixStateState_two_zero : sixStateState 2 0 = qubitKet0 := rfl

@[simp] theorem sixStateState_two_one : sixStateState 2 1 = qubitBasis 1 := rfl

/-- **Bob's six-state measurement in basis `i`:** the two-outcome projective measurement of the `±1`
observable `sixStateObservable i` (`Observable.signMeasurement`, outcome `0 ↔ +1`, `1 ↔ −1`). The
outcome index is Bob's result bit. -/
def sixStateMeasurement (i : Fin 3) : Measurement (Fin 2) qubit :=
  (sixStateObservable i).signMeasurement (sixStateObservable_op_mul_self i)

end AxQM
