/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.PauliEigen
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.ControlBranchExt

/-!
# AxQM.Basic.API — measuring an observable with a Hadamard-controlled-`U` circuit

The operator-level form of Nielsen & Chuang's Exercise 4.34 ("Measuring an operator"): the circuit
that implements a projective measurement of a single-qubit `±1` observable `U` (an operator that is
both Hermitian and unitary, hence both an observable and a gate) using one ancilla qubit, a
controlled-`U`, and two Hadamards.

## Main declarations
* `Evolution.toObservable U hsa` — a **Hermitian gate viewed as an observable**: a unitary `U` (an
  `Evolution`) that is additionally self-adjoint (`IsSelfAdjoint U.op`) is packaged as an
  `Observable`. `Evolution.toObservable_op_mul_self` records the resulting **involution** `U² = I`
  (from unitary ∧ self-adjoint), the hypothesis every `±1`-observable API needs.
* `measureObservableCircuit U` — the **circuit** `(H ⊗ 1) · C(U) · (H ⊗ 1)` on `qubit ⊗ qubit`
  (ancilla = left/control qubit; target = right qubit), an `Evolution`.
* `measureObservableCircuit_op_qubitBasisZero_tmul` — **the circuit action**: with the ancilla
  prepared in `|0⟩`, the circuit sends `|0⟩ ⊗ |ψ⟩` to `|0⟩ ⊗ P₊|ψ⟩ + |1⟩ ⊗ P₋|ψ⟩`, where `P₊ = (I +
  U)/2` and `P₋ = (I − U)/2` are the eigenprojectors of `U`. Stated at the raw operator level (`(I ±
  U)/2` applied to a target vector `x`) so it needs no self-adjointness hypothesis.
* `measureObservableCircuit_op_qubitBasisZero_tmul_signMeasurement` — the same, with the target
  components written as the measurement operators `M₀`, `M₁` of `Observable.signMeasurement` — the
  projective measurement **of the observable `U`** (N&C §2.2.5). This is the precise sense in which
  the circuit *implements a measurement of `U`*: the theorem proves the *pre-measurement* correlated
  state `|0⟩ ⊗ M₀x + |1⟩ ⊗ M₁x`, whose `|i⟩`-ancilla branch carries the target through the `i`-th
  measurement operator of that measurement. A computational-basis measurement of the ancilla (read
  `0 ↦ +1`, `1 ↦ −1`) then collapses the target onto `Mᵢx` with Born weight `‖Mᵢx‖²` — the
  statistics and post-measurement states of the sign measurement of `U`. That last step is the
  physical interpretation of the correlation, not part of what this theorem states.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A Hermitian gate as an observable.** A unitary evolution `U` that is
additionally self-adjoint is an observable with the same underlying operator.
This is what N&C's Exercise 4.34 means by regarding `U` as both an observable and a gate: the
gate is `U` itself, and the observable is `U.toObservable hsa`. -/
def Evolution.toObservable (U : Evolution S) (hsa : IsSelfAdjoint U.op) : Observable S where
  op := U.op
  selfAdjoint := hsa

/-- The underlying operator of `U.toObservable` is `U.op`. -/
@[simp]
theorem Evolution.toObservable_op (U : Evolution S) (hsa : IsSelfAdjoint U.op) :
    (U.toObservable hsa).op = U.op := rfl

/-- **A self-adjoint unitary is an involution:** `U² = I`. From unitarity `U† U = I` and
self-adjointness `U† = U`, so `U U = U† U = I`. -/
theorem Evolution.toObservable_op_mul_self (U : Evolution S) (hsa : IsSelfAdjoint U.op) :
    (U.toObservable hsa).op * (U.toObservable hsa).op = 1 := by
  rw [Evolution.toObservable_op]
  have hu : star U.op * U.op = 1 := (Unitary.mem_iff.mp U.unitary).1
  have hsa' : star U.op = U.op := hsa
  rwa [hsa'] at hu

/-- **The Hadamard-controlled-`U` measurement circuit** of Nielsen & Chuang Exercise 4.34: the
`Evolution` on `qubit ⊗ S` given by `(H ⊗ 1) · C(U) · (H ⊗ 1)` — a Hadamard on the control
(left/ancilla) qubit, then the controlled-`U` gate, then another Hadamard on the control.
Reading the ancilla in the computational basis after this circuit is a measurement of the
observable `U`.

The target register `S` is *arbitrary* (not just a single qubit).
-/
def measureObservableCircuit (U : Evolution S) : Evolution (qubit ⊗ S) :=
  (hadamardGate.onLeft S).comp ((controlledUnitary U).comp (hadamardGate.onLeft S))

/-- **The measurement circuit's action**. With the ancilla prepared in `|0⟩`, the circuit sends `|0⟩
⊗ x` to `|0⟩ ⊗ ½(I + U)x + |1⟩ ⊗ ½(I − U)x`: the ancilla `|0⟩` branch carries the target through
the `+1` eigenprojector `P₊ = ½(I + U)` and the `|1⟩` branch through the `−1` eigenprojector `P₋
= ½(I − U)`.

Stated at the raw operator level (`½(x ± U·x)`), so it holds for *every* target vector `x` and
needs no self-adjointness hypothesis; the eigenprojector / measurement readings are the
corollaries below.
-/
theorem measureObservableCircuit_op_qubitBasisZero_tmul (U : Evolution S) (x : S.space) :
    (measureObservableCircuit U).op ((qubitBasis 0).vec ⊗ₜ[ℂ] x)
      = (qubitBasis 0).vec ⊗ₜ[ℂ] ((2⁻¹ : ℂ) • (x + U.op x))
        + (qubitBasis 1).vec ⊗ₜ[ℂ] ((2⁻¹ : ℂ) • (x - U.op x)) := sorry

/-- **The circuit implements the measurement of the observable `U`.**  With the ancilla in `|0⟩`,
the circuit sends `|0⟩ ⊗ x` to `|0⟩ ⊗ M₀x + |1⟩ ⊗ M₁x`, where `M₀`, `M₁` are the two measurement
operators of `Observable.signMeasurement` — the projective measurement *of the observable `U`*
(N&C §2.2.5), with `M₀ = P₊` (outcome `+1`) and `M₁ = P₋` (outcome `−1`).  Thus reading the ancilla
in the computational basis after the circuit and interpreting `0 ↦ +1`, `1 ↦ −1` realises exactly
that measurement: outcome `i` occurs with probability `‖Mᵢx‖²` and leaves the target in the
(unnormalised) collapsed state `Mᵢx` — an eigenvector of `U` with the corresponding eigenvalue. -/
theorem measureObservableCircuit_op_qubitBasisZero_tmul_signMeasurement (U : Evolution S)
    (hsa : IsSelfAdjoint U.op) (x : S.space) :
    (measureObservableCircuit U).op ((qubitBasis 0).vec ⊗ₜ[ℂ] x)
      = (qubitBasis 0).vec ⊗ₜ[ℂ]
          (((U.toObservable hsa).signMeasurement (U.toObservable_op_mul_self hsa)).op 0 x)
        + (qubitBasis 1).vec ⊗ₜ[ℂ]
          (((U.toObservable hsa).signMeasurement (U.toObservable_op_mul_self hsa)).op 1 x) := sorry

end AxQM
