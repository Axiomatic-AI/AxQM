/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.BellBasis
import AxQM.Basic.API.Associator
import AxQM.Basic.Measurement

/-!
# AxQM.Basic.API — Pauli corrections and Bell-basis measurement

The two non-CNOT resources of Nielsen & Chuang **Problem 4.6** ("Universality with prior
entanglement"): the **single-qubit unitaries** used as teleportation corrections (the Pauli
byproduct gates) and the **Bell-basis measurement** of a qubit pair.  Together with the
four-qubit entangled resource state (a later chunk), these implement a CNOT by gate
teleportation and so form a universal set.

## Main declarations
* `pauliZGate` — the Pauli-`Z` gate as an `Evolution qubit`, built from
  `Concrete.pauliZ = !![1,0;0,-1]` through `Matrix.toEuclideanCLM`; unitarity is transported from
  `Concrete.pauliZ_mem_unitaryGroup`.
* `pauliByproduct x y` — the **Pauli byproduct** correction `X^y Z^x` (`x, y : Fin 2`) as an
  `Evolution qubit`, i.e. a genuine *single-qubit unitary* (resource #1 of Problem 4.6): the
  correction applied to the teleported qubit for the Bell-measurement outcome `(x, y)`.
* `bellMeasurement` — the **Bell-basis measurement** of a qubit pair (resource #2 of Problem 4.6):
  the projective measurement `Measurement.ofOrthonormalBasis bellBasis` of `qubit ⊗ qubit`, with
  outcomes indexed by `Fin 2 × Fin 2` and operators the Bell projectors `|β_xy⟩⟨β_xy|`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- The **Pauli-`Z` gate** `Z` (the phase flip) as a closed-system `Evolution` of the qubit. -/
def pauliZGate : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliZ
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) Concrete.pauliZ_mem_unitaryGroup

/-- The **Pauli byproduct** `X^y Z^x` (`x, y : Fin 2`) as an `Evolution qubit`: the single-qubit
unitary correction applied to the teleported qubit given a Bell measurement outcome `(x, y)`.  For
`y = 0` the `X` factor is the identity, for `y = 1` it is `pauliXGate`; likewise `x` selects
`pauliZGate`.  Being a value of `Evolution`, it is manifestly an admissible
single-qubit gate — resource #1 of Problem 4.6. -/
def pauliByproduct (x y : Fin 2) : Evolution qubit :=
  (if y = 0 then Evolution.id else pauliXGate).comp (if x = 0 then Evolution.id else pauliZGate)

/-- The **Bell-basis measurement** of a qubit pair (Problem 4.6 resource #2). It is a genuine
`Measurement`: the ability to Bell-measure a pair of qubits is exactly a value of
this primitive. -/
def bellMeasurement : Measurement (Fin 2 × Fin 2) (qubit ⊗ qubit) :=
  Measurement.ofOrthonormalBasis bellBasis

/-- **The POVM elements of the Bell measurement (Nielsen & Chuang Exercise 4.33).**  The POVM
element for outcome `(x, y)` is the projector onto the Bell state,
`bellMeasurement.toPOVM.elements (x, y) = |β_xy⟩⟨β_xy|`.  Since each measurement operator is a unit
rank-one projector it equals its own POVM element, so the four Bell projectors are simultaneously
the measurement operators and the POVM elements — the answer N&C asks for. -/
theorem bellMeasurement_toPOVM_elements_eq_bellProjector (x y : Fin 2) :
    bellMeasurement.toPOVM.elements (x, y)
      = ((InnerProductSpace.rankOne ℂ) (bellState x y).vec) (bellState x y).vec := sorry

end AxQM
