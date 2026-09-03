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
# AxQM.Basic.API — the BB84 states, bases, and measurement

The infrastructure behind the BB84 quantum-key-distribution protocol (Nielsen &
Chuang §12.6.3, p. 587): Alice's four encoding states `|ψ_{ab}⟩`, the two conjugate measurement
bases (`Z` for `b = 0`, `X` for `b = 1`), and Bob's projective measurement in a chosen basis.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The BB84 measurement observable for basis bit `b`.** Bob measures the Pauli `Z` observable
when `b = 0` (the computational basis `{|0⟩, |1⟩}`) and the Pauli `X` observable when `b = 1` (the
Hadamard basis `{|+⟩, |−⟩}`) — the two conjugate bases of the protocol (N&C §12.6.3). -/
def bb84Observable (b : Fin 2) : Observable qubit := ![pauliZObservable, pauliXObservable] b

@[simp] theorem bb84Observable_zero : bb84Observable 0 = pauliZObservable := rfl

@[simp] theorem bb84Observable_one : bb84Observable 1 = pauliXObservable := rfl

/-- Each BB84 basis observable is a self-adjoint **involution**: `(bb84Observable b)² = 1`, so its
projective measurement is a genuine two-outcome `signMeasurement`. -/
theorem bb84Observable_op_mul_self (b : Fin 2) :
    (bb84Observable b).op * (bb84Observable b).op = 1 := by
  fin_cases b
  · simpa using pauliZObservable_op_mul_self
  · simpa using pauliXObservable_op_mul_self

/-- **Alice's BB84 encoding state `|ψ_{ab}⟩`** of data bit `a` in basis `b` (N&C eqs.
12.180–12.183): `|ψ_{00}⟩ = |0⟩`, `|ψ_{10}⟩ = |1⟩` in the computational basis (`b = 0`), and
`|ψ_{01}⟩ = |+⟩`, `|ψ_{11}⟩ = |−⟩` in the Hadamard basis (`b = 1`). Each is the `(-1)^a`-eigenstate
of the basis
observable `bb84Observable b`. -/
def bb84State (a b : Fin 2) : PureState qubit :=
  ![![qubitKet0, qubitPlus], ![qubitBasis 1, qubitMinus]] a b

@[simp] theorem bb84State_zero_zero : bb84State 0 0 = qubitKet0 := rfl

@[simp] theorem bb84State_zero_one : bb84State 0 1 = qubitPlus := rfl

@[simp] theorem bb84State_one_zero : bb84State 1 0 = qubitBasis 1 := rfl

@[simp] theorem bb84State_one_one : bb84State 1 1 = qubitMinus := rfl

/-- **Bob's BB84 measurement in basis `b`:** the two-outcome projective measurement of the `±1`
observable `bb84Observable b` (`Observable.signMeasurement`, outcome `0 ↔ +1`, `1 ↔ −1`). The
outcome index is Bob's result bit `a'`. -/
def bb84Measurement (b : Fin 2) : Measurement (Fin 2) qubit :=
  (bb84Observable b).signMeasurement (bb84Observable_op_mul_self b)

end AxQM
