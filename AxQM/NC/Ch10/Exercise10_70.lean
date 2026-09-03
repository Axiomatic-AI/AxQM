/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.EigenspaceCollapse
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.Teleportation
import AxQM.Basic.Composite
import AxQM.NC.Ch10.Exercise10_6

/-!
# Nielsen & Chuang, Exercise 10.70 (Z errors in the fault-tolerant measurement ancilla)

*(N&C p. 491.)*

Show Z errors in the ancilla do not propagate to encoded data but give an incorrect measurement
result.

* `measureObservableCircuitZError` — the primitive with a `Z` error on the control between `C(M)`
  and the decoding `H`, and the error's position on that wire being immaterial.
* `measureObservableCircuitZError_evolvePure_qubitBasisZero_of_eigenstate` — the concrete reading on
  a `+1` eigenstate `x` of `M`: ideal reports `0` (correct), corrupted reports `1` (incorrect), and
  in both the data factor is still `x` (unchanged).
* `blockXObservable_hasEigenstate_blockPhaseFlip_catBlockState` — (B), cat level —
  `blockXObservable_hasEigenstate_blockPhaseFlip_catBlockState`: a `Z` error on any one of the three
  ancilla qubits makes the sign readout `blockXObservable` report the *opposite* eigenvalue
  `(−1)^{σ+1}` (incorrect).
* `transversalCoupling` — (A), transversal level — `transversalCoupling` is the transversal
  `C(M′)⊗C(M′)⊗C(M′)` coupling of the three (ancilla, data) pairs;
  `transversalCoupling_comm_transversalAncillaPhaseError` shows a `Z` error on any ancilla qubit
  commutes past the coupling, so it never becomes a data operation.
* `transversalAncillaPhaseError`
* `transversalCoupling_comm_transversalAncillaPhaseError` — (A), transversal level —
  `transversalCoupling` is the transversal `C(M′)⊗C(M′)⊗C(M′)` coupling of the three (ancilla, data)
  pairs; `transversalCoupling_comm_transversalAncillaPhaseError` shows a `Z` error on any ancilla
  qubit commutes past the coupling, so it never becomes a data operation.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The atomic mechanism: a single control/target measurement pair -/

/-- The operator-measurement primitive `measureObservableCircuit M` **with a `Z` error on the
ancilla** (the control qubit), inserted between the controlled-`M` gate and the decoding `Hadamard`:
`(H ⊗ 1) · (Z ⊗ 1) · C(M) · (H ⊗ 1)`.  This models a `Z` error "in the ancilla" of the
fault-tolerant measurement of `M`. -/
def measureObservableCircuitZError (M : Evolution S) : Evolution (qubit.compose S) :=
  (hadamardGate.onLeft S).comp
    ((pauliZGate.onLeft S).comp ((controlledUnitary M).comp (hadamardGate.onLeft S)))

/-- **(B) A `Z` error gives an incorrect measurement result, with the data unaffected.**  On the
same `+1` eigenstate `x` of `M` for which the ideal circuit reads `0`, the corrupted circuit sends
`|0⟩ ⊗ x` to `|1⟩ ⊗ x`: the ancilla now reads `1` — the *wrong* outcome — while the data factor is
still `x`, unchanged.  Thus the `Z` error does not propagate to the encoded data but does produce an
incorrect measurement result. -/
theorem measureObservableCircuitZError_evolvePure_qubitBasisZero_of_eigenstate
    (M : Evolution S) (x : PureState S) (hx : M.evolvePure x = x) :
    (measureObservableCircuitZError M).evolvePure ((qubitBasis 0).tmul x)
      = (qubitBasis 1).tmul x := sorry

/-! ### The genuine three-qubit cat ancilla of Figure 10.28: incorrect readout (claim B)

The atomic picture above encodes the ancilla in a **single** control qubit; the fault-tolerant
measurement of N&C Fig. 10.28 instead uses a three-qubit **cat ancilla**
`catBlockState σ = (|000⟩ + (−1)^σ |111⟩)/√2`, one qubit per data qubit.  Its measurement outcome is
the sign `σ`, read by the sign-observable `blockXObservable = X⊗X⊗X`, whose eigenvalue on
`catBlockState σ` is `(−1)^σ`. -/

/-- **(B), cat level — a single `Z` error on the cat ancilla flips the measurement readout.**  A
phase-flip `Z` error on *any* of the three ancilla qubits sends `catBlockState σ ↦ catBlockState
(σ+1)`, so the errored ancilla is read by
`blockXObservable` with the eigenvalue `(−1)^{σ+1}` — the **opposite** of the ideal `(−1)^σ` (since
`σ+1 ≠ σ` in `Fin 2`): the measured result is flipped, i.e. incorrect. -/
theorem blockXObservable_hasEigenstate_blockPhaseFlip_catBlockState (i : Fin 3) (σ : Fin 2) :
    blockXObservable.HasEigenstate ((-1 : ℝ) ^ ((σ + 1 : Fin 2) : ℕ))
      ((blockPhaseFlip i).evolvePure (catBlockState σ)) := sorry

/-! ### The transversal coupling: `Z` errors do not propagate to the data (claim A)

The ancilla–data coupling of Fig. 10.28 is **transversal**: ancilla qubit `i` is the *control* of a
`controlled-M′` gate on data qubit `i`, and the three (ancilla, data) pairs are coupled
independently.  Working over an arbitrary data-qubit system `D`, this is the tensor product of three
`controlledUnitary M′` gates on the register of three (ancilla, data) pairs. -/

variable {D : QSystem}

/-- **The transversal controlled-`M′` coupling of Figure 10.28.**  Three independent (ancilla, data)
pairs, each coupled by a `controlledUnitary M′` whose control is the ancilla qubit (the left factor
of `qubit ⊗ D`) and whose target is the data qubit: `C(M′) ⊗ C(M′) ⊗ C(M′)`.  If the cat ancilla is
`|000⟩` nothing is done to the data; if `|111⟩` the transversal `M = M′⊗M′⊗M′` is applied — as in
N&C. -/
def transversalCoupling (M : Evolution D) :
    Evolution ((qubit.compose D).compose ((qubit.compose D).compose (qubit.compose D))) :=
  (controlledUnitary M) ⊗ ((controlledUnitary M) ⊗ (controlledUnitary M))

/-- **A phase-flip `Z` error on the `i`-th ancilla qubit** of the transversal coupling — the control
of pair `i` (the left factor of that pair's `qubit ⊗ D`) — acting as the identity on the two other
pairs. -/
def transversalAncillaPhaseError :
    Fin 3 → Evolution ((qubit.compose D).compose ((qubit.compose D).compose (qubit.compose D)))
  | 0 => (pauliZGate.onLeft D) ⊗
      ((Evolution.id : Evolution (qubit.compose D)) ⊗ (Evolution.id : Evolution (qubit.compose D)))
  | 1 => (Evolution.id : Evolution (qubit.compose D)) ⊗
      ((pauliZGate.onLeft D) ⊗ (Evolution.id : Evolution (qubit.compose D)))
  | 2 => (Evolution.id : Evolution (qubit.compose D)) ⊗
      ((Evolution.id : Evolution (qubit.compose D)) ⊗ (pauliZGate.onLeft D))

/-- **(A) — a `Z` error on the ancilla commutes past the coupling, so it does not propagate to the
data.**  A phase-flip `Z` error on ancilla qubit `i` commutes with the transversal coupling:
`transversalCoupling M · Zᵢ = Zᵢ · transversalCoupling M`.  Because the ancilla qubits are the
*controls*, the error slides through the ancilla–data interaction unchanged and never becomes an
operation on the data.  Composing several such (mutually commuting) errors shows that
*multiple* ancilla `Z` errors likewise do not propagate. -/
theorem transversalCoupling_comm_transversalAncillaPhaseError (M : Evolution D) (i : Fin 3) :
    (transversalCoupling M).comp (transversalAncillaPhaseError i)
      = (transversalAncillaPhaseError i).comp (transversalCoupling M) := sorry

end AxQM
