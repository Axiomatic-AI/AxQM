/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EigenspaceCollapse
import AxQM.Basic.API.UnitaryBlochRotation
import AxQM.Concrete.SXCorrectionMatrix
import AxQM.NC.Ch10.Exercise10_70

/-!
# Nielsen & Chuang, Exercise 10.71 (Fault-tolerant measurement of `M = e^{-iπ/4}SX`)

*(N&C p. 491.)*

Verify that for M=e^{-ipi/4}SX the described procedure is a fault-tolerant way to measure M.

* `sxCorrectionGate`
* `sxCorrectionEigenstatePlus`
* `sxCorrectionEigenstateMinus`
* `measureObservableCircuit_sxCorrectionGate_ketZero_eigenstatePlus`
* `measureObservableCircuit_sxCorrectionGate_ketZero_eigenstateMinus`
* `zsxGate`
* `transversalCoupling_zsxGate_comm_ancillaPhaseError`
* `measureObservableCircuitZError_sxCorrectionGate_eigenstatePlus` — (B) a `Z` error instead flips
  the measurement result while leaving the data unchanged —
  `measureObservableCircuitZError_sxCorrectionGate_eigenstatePlus` (Ex. 10.70's claim B for `M`).
-/

open Matrix Complex

noncomputable section

namespace AxQM

/-- **`M = e^{-iπ/4}SX` as the unitary `Evolution qubit`** measured by the Hadamard-test circuit.
`M` is Hermitian and involutive, i.e. a self-adjoint unitary, so this gate *is* a `±1` observable
— the operator whose fault-tolerant measurement is the subject of the exercise (and which creates
the π/8-gate ancilla). -/
def sxCorrectionGate : Evolution qubit := unitaryGate Concrete.mMatrix_mem_unitaryGroup

/-- The **`+1` eigenstate `|Θ⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2`** of `M` as a qubit `PureState`
(`Concrete.thetaVec`, normalized since `‖invSqrt2‖² + ‖invSqrt2·e^{iπ/4}‖² = ½ + ½ = 1`). This is
precisely the ancilla produced by the fault-tolerant π/8 gate of Exercise 10.66. -/
def sxCorrectionEigenstatePlus : PureState qubit where
  vec := WithLp.toLp 2 Concrete.thetaVec
  normalized := by
    have h : ‖(WithLp.toLp 2 Concrete.thetaVec : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Concrete.thetaVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        norm_mul, Concrete.norm_tMatrix_one_one, mul_one, Concrete.norm_invSqrt2_sq]
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, Real.sqrt_one]
    exact h

/-- The **`−1` eigenstate `|Θ⁻⟩ = (|0⟩ − e^{iπ/4}|1⟩)/√2`** of `M` as a qubit `PureState`
(`Concrete.thetaMinusVec`, normalized as for `|Θ⟩`). -/
def sxCorrectionEigenstateMinus : PureState qubit where
  vec := WithLp.toLp 2 Concrete.thetaMinusVec
  normalized := by
    have h : ‖(WithLp.toLp 2 Concrete.thetaMinusVec : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Concrete.thetaMinusVec, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, norm_neg, norm_mul, Concrete.norm_tMatrix_one_one, mul_one,
        Concrete.norm_invSqrt2_sq]
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, Real.sqrt_one]
    exact h

/-- **The measurement circuit reads `M`'s `+1` eigenvalue as outcome `0`.** Running the standard
observable-measurement circuit `measureObservableCircuit` (the Hadamard-test of
Figs. 10.13/10.26 that the fault-tolerant procedure implements) on `|0⟩ ⊗ |Θ⟩`, with `|Θ⟩` the `+1`
eigenstate of `M`, leaves the ancilla in `|0⟩` and the data unchanged: the measurement result `0`
faithfully reports the eigenvalue `+1`. -/
theorem measureObservableCircuit_sxCorrectionGate_ketZero_eigenstatePlus :
    (measureObservableCircuit sxCorrectionGate).evolvePure
        ((qubitBasis 0).tmul sxCorrectionEigenstatePlus)
      = (qubitBasis 0).tmul sxCorrectionEigenstatePlus := sorry

/-- **The measurement circuit reads `M`'s `−1` eigenvalue as outcome `1`.** On `|0⟩ ⊗ |Θ⁻⟩`, with
`|Θ⁻⟩` the `−1` eigenstate of `M`, the circuit flips the ancilla to `|1⟩` and leaves the data
unchanged: the measurement result `1` faithfully reports the eigenvalue `−1`. Together with the
`+1` case this is the correctness of the (idealised) measurement of `M`. -/
theorem measureObservableCircuit_sxCorrectionGate_ketZero_eigenstateMinus :
    (measureObservableCircuit sxCorrectionGate).evolvePure
        ((qubitBasis 0).tmul sxCorrectionEigenstateMinus)
      = (qubitBasis 1).tmul sxCorrectionEigenstateMinus := sorry

/-! ### The transversal correction gate, and the fault-tolerance of the procedure for `M`

The remaining ingredients specialise the **fault-tolerant measurement procedure** of Figure 10.28 to
`M = e^{-iπ/4}SX`. The generic fault-tolerance analysis says that a single fault in the cat-ancilla
preparation and verification leaves at most one `X`/`Y` error in the accepted ancilla
(Exercise 10.69, entirely `M`-independent), and that `Z` errors on the ancilla behave as
analysed in Exercise 10.70. What is
`M`-specific is that the transversal coupling of Figure 10.28 is realised — by the "slight
modification" of N&C p. 491 — as transversal **controlled-`ZSX`** followed by seven `T` gates on the
ancilla. The two claims of Exercise 10.70 therefore hold *for this procedure* by instantiation:

* **(A) `Z` errors on the ancilla do not propagate to the encoded data**, because the coupling is a
  transversal *controlled* operation with the ancilla qubits as the **controls**, and a `Z` on a
  control commutes with a controlled gate (`transversalCoupling_zsxGate_comm_ancillaPhaseError`).
* **(B) a `Z` error flips the measurement result while leaving the data untouched**
  (`measureObservableCircuitZError_sxCorrectionGate_eigenstatePlus`).
-/

/-- **The per-qubit transversal correction `ZSX` as a qubit `Evolution`.** For `M = e^{-iπ/4}SX` the
"slight modification" of N&C p. 491 realises the controlled-`M` of Figure 10.28 by applying
controlled-`ZSX` transversally to each (ancilla, data) pair (its Clifford part: `X^{⊗7}` is
logical `X̄` and `(ZS)^{⊗7}` logical `S̄`), the non-Clifford scalar `e^{-iπ/4}` being supplied
separately by seven ancilla `T` gates. -/
def zsxGate : Evolution qubit := unitaryGate Concrete.zsxMatrix_mem_unitaryGroup

/-- **(A) A `Z` error on the ancilla does not propagate to the data, for the `M = e^{-iπ/4}SX`
procedure.** The transversal controlled-`ZSX` coupling of the ancilla to the data
(`transversalCoupling zsxGate`, three (ancilla, data) pairs as in Figure 10.28) commutes with a
phase-flip `Z` error on any ancilla qubit `i`: `(C(ZSX)^{⊗3}) · Zᵢ = Zᵢ · (C(ZSX)^{⊗3})`. The
seven ancilla `T` gates of the slight modification are diagonal, so they too commute with an
ancilla `Z`; thus the full modified coupling propagates no `Z` error to the data — claim (A) of
the fault-tolerance analysis for this procedure. -/
theorem transversalCoupling_zsxGate_comm_ancillaPhaseError (i : Fin 3) :
    (transversalCoupling zsxGate).comp (transversalAncillaPhaseError i)
      = (transversalAncillaPhaseError i).comp (transversalCoupling zsxGate) := sorry

/-- **(B) A `Z` error on the ancilla flips the `M`-measurement result but leaves the data
unaffected.** On `|0⟩ ⊗ |Θ⟩` with `|Θ⟩` the `+1` eigenstate of `M`, the ideal measurement
circuit reads outcome `0` (`measureObservableCircuit_sxCorrectionGate_ketZero_eigenstatePlus`,
the correct report of eigenvalue `+1`); a `Z` error on the ancilla instead sends `|0⟩ ⊗ |Θ⟩` to
`|1⟩ ⊗ |Θ⟩` — the ancilla now reads the *wrong* outcome `1`, while the data factor is still
`|Θ⟩`, unchanged. -/
theorem measureObservableCircuitZError_sxCorrectionGate_eigenstatePlus :
    (measureObservableCircuitZError sxCorrectionGate).evolvePure
        ((qubitBasis 0).tmul sxCorrectionEigenstatePlus)
      = (qubitBasis 1).tmul sxCorrectionEigenstatePlus := sorry

end AxQM
