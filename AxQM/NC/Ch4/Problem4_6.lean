/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.GateTeleportCorrection
import AxQM.Basic.API.GateTeleportChannelRef
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.CompositeMeasurement
import AxQM.Basic.API.Swap
import AxQM.Basic.API.SchmidtDecomposition
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.ControlMeasurementCommute
import AxQM.Basic.Composite
import AxQM.Basic.PartialTrace
import AxQM.Basic.Evolution
import AxQM.Basic.API.TensorPowSplit
import AxQM.Basic.API.BlockGatePlacement
import AxQM.Basic.API.LeftPairGate
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Core.McNotCircuitEvolution
import AxQM.Basic.API.WirePermutation
import AxQM.Basic.API.Qubit
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import AxQM.Concrete.CnotPairGatherPermutation

/-!
# Nielsen & Chuang, Problem 4.6 (Universality with prior entanglement)

*(N&C p. 213.)*

Show single-qubit unitaries + Bell-basis measurement + 4-qubit-state prep is universal.

* `qubitTensorPowTwoIso`
* `qubitBackPairReshape`
* `CnotWiresRealized`
* `placedSingleQubit`
* `IsResourceGeneratorWires`
* `measurementResourceSetWires_realizes_of_universal`
-/

namespace AxQM

open scoped TensorProduct

/-!
### Toward the `n`-wire register: `CNOT` on a designated wire pair
-/

/-- The two-wire register collapse `qubit ^⊗ₛ 2 ≃ₛ qubit ⊗ qubit`. -/
noncomputable def qubitTensorPowTwoIso : (qubit.tensorPow 2).Iso (qubit ⊗ qubit) :=
  (QSystem.tensorPowAdd qubit 1 1).trans (qubit.tensorPowOne.symm.tmul qubit.tensorPowOne.symm)

/-- **The back-pair reshape** `qubit ^⊗ₛ (n+2) ≃ₛ (qubit ^⊗ₛ n) ⊗ (qubit ⊗ qubit)`. -/
noncomputable def qubitBackPairReshape (n : ℕ) :
    (qubit.tensorPow (n + 2)).Iso ((qubit.tensorPow n) ⊗ (qubit ⊗ qubit)) :=
  (QSystem.tensorPowAdd qubit n 2).trans
    ((QSystem.Iso.refl (qubit.tensorPow n)).tmul qubitTensorPowTwoIso)

/-!
### `CNOT` on an arbitrary wire pair (completing the `CNOT`-generator realization)

Faithful universality decomposes an arbitrary
unitary into `CNOT`s addressed to *every* ordered wire pair `(i, j)` together with single-qubit
gates (N&C's given, `{CNOT, single-qubit}` universal), so the resource must realize `CNOT` on an
**arbitrary** control/target pair `i ≠ j`, not merely the back pair.

An arbitrary pair is addressed by **conjugating with a wire-permutation reshape**
`qubit.tensorPowCongr σ`, where `σ := Concrete.cnotPairGatherPerm n i j` gathers the back-pair
positions `(n, n+1)` onto `(i, j)`.  Conjugation is a `State.congr` / `PureState.congr`
transport (a register relabelling — free bookkeeping, not a resource gate), so no extra physical
operation enters: the gadget is applied to the physical wires `(i, j)` directly, and addressing
them is only a choice of which qubits to Bell-measure and which four to prepare `|χ⟩` on.
-/

/-- **The resource set realizes `CNOT` on _every_ ordered wire pair**, as a proposition (Nielsen &
Chuang, Problem 4.6): for every control/target pair `i ≠ j` of the `(n+2)`-wire register, every
input pure state `ψ` (possibly entangling the two `CNOT` wires with the other `n`), and every
Bell-measurement outcome `(p, q)`, the gate-teleportation gadget *addressed to wires `(i, j)`* —
the back-pair gadget conjugated by the addressing reshape `qubit.tensorPowCongr
(Concrete.cnotPairGatherPerm n i j)` — sends the register to `(Evolution.placedMcNot {i}
j).evolvePure ψ`, i.e. the canonical `CNOT` on `(i, j)` applied to `ψ`, independent of the
outcome.
-/
def CnotWiresRealized (n : ℕ) : Prop :=
  ∀ (i j : Fin (n + 2)) (hij : i ≠ j) (ψ : PureState (qubit.tensorPow (n + 2)))
    (p q : Fin 2 × Fin 2)
    (hp : (bellPairsMeasurement.onRight (qubit.tensorPow n)).bornProb
        (gateTeleportRegisterGenRef (qubit.tensorPow n)
          (PureState.congr (qubitBackPairReshape n)
            (PureState.congr (qubit.tensorPowCongr (Concrete.cnotPairGatherPerm n i j)).symm
              ψ))).toState
        (p, q) ≠ 0),
    ((((((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).onRight
                  (qubit.tensorPow n)).evolve
            ((bellPairsMeasurement.onRight (qubit.tensorPow n)).postMeasurement
              (gateTeleportRegisterGenRef (qubit.tensorPow n)
                (PureState.congr (qubitBackPairReshape n)
                  (PureState.congr (qubit.tensorPowCongr (Concrete.cnotPairGatherPerm n i j)).symm
                    ψ))).toState (p, q) hp)).congr
          (QSystem.Iso.leftComm (qubit.tensorPow n) ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))
            (qubit ⊗ qubit))).reducedRight.congr (qubitBackPairReshape n).symm).congr
        (qubit.tensorPowCongr (Concrete.cnotPairGatherPerm n i j))
      = ((Evolution.placedMcNot {i} j (by rw [Finset.mem_singleton]; exact Ne.symm hij)).evolvePure
          ψ).toState

/-!
### The `n`-wire universality assembly (Nielsen & Chuang, Problem 4.6)
-/

/-- **A single-qubit unitary placed on wire `i`** of the register `qubit ^⊗ₛ (n+2)` (Nielsen &
Chuang, Problem 4.6): `U` acting on wire `i`, the identity on the other `n+1` wires. Built by
placing `U` on the head wire (`U.onLeft`, i.e. `U ⊗ 1`, through the head-peel reshape
`QSystem.tensorPowSuccHead`) and relabelling the head wire to wire `i` by the wire-swap reshape
`qubit.tensorPowCongr (Equiv.swap 0 i)` — a register relabelling (free wire addressing,
not a resource gate), so no extra physical operation enters. -/
noncomputable def placedSingleQubit (n : ℕ) (i : Fin (n + 2)) (U : Evolution qubit) :
    Evolution (qubit.tensorPow (n + 2)) :=
  Evolution.congr (qubit.tensorPowCongr (Equiv.swap 0 i))
    (Evolution.congr (QSystem.tensorPowSuccHead qubit (n + 1)).symm
      (U.onLeft (qubit.tensorPow (n + 1))))

/-- **The measurement resource set's generating family on the `(n+2)`-wire register** (Nielsen &
Chuang, Problem 4.6): the canonical wire-addressed `CNOT` `Evolution.placedMcNot {i}
j` on every ordered control/target pair `i ≠ j`, and every single-qubit unitary on every wire
(`placedSingleQubit n i U`). N&C's premise that `{CNOT, single-qubit}` is universal is the
statement that this family generates every `(n+2)`-wire evolution. -/
def IsResourceGeneratorWires (n : ℕ) (E : Evolution (qubit.tensorPow (n + 2))) : Prop :=
  (∃ (i j : Fin (n + 2)) (hij : i ≠ j),
      E = Evolution.placedMcNot {i} j (by rw [Finset.mem_singleton]; exact Ne.symm hij)) ∨
    (∃ (i : Fin (n + 2)) (U : Evolution qubit), E = placedSingleQubit n i U)

/-- **The gates the measurement resource set implements on the `(n+2)`-wire register.**  Built by
composition from single-qubit unitaries on any wire applied directly (resource #1 — the
`singleQubitWire` constructor, `placedSingleQubit n i U`) and the canonical `CNOT` on any
ordered wire pair realized by gate teleportation (the `cnotWire` constructor). The `cnotWire`
constructor **carries** the realization witness `CnotWiresRealized n`.
-/
inductive ResourceImplementsWires (n : ℕ) : Evolution (qubit.tensorPow (n + 2)) → Prop
  /-- The identity is realized (do nothing). -/
  | one : ResourceImplementsWires n 1
  /-- Realizable gates compose (run one protocol after the other). -/
  | comp {U V : Evolution (qubit.tensorPow (n + 2))} :
      ResourceImplementsWires n U → ResourceImplementsWires n V →
      ResourceImplementsWires n (U.comp V)
  /-- A single-qubit unitary on any wire `i`, `placedSingleQubit n i U`, is realized directly
  (resource #1). -/
  | singleQubitWire (i : Fin (n + 2)) (U : Evolution qubit) :
      ResourceImplementsWires n (placedSingleQubit n i U)
  /-- The canonical `CNOT` on any ordered wire pair `(i, j)` is realized by gate teleportation,
  witnessed by `CnotWiresRealized n`. -/
  | cnotWire (i j : Fin (n + 2)) (hij : i ≠ j) (h : CnotWiresRealized n) :
      ResourceImplementsWires n
        (Evolution.placedMcNot {i} j (by rw [Finset.mem_singleton]; exact Ne.symm hij))

/-- **The measurement resource set is universal on every register** (Nielsen & Chuang, Problem 4.6 —
the Gottesman–Chuang reduction). Assuming N&C's given that the gate
family `{CNOT, single-qubit}` is universal on the `(n+2)`-wire register — every evolution of
`qubit ^⊗ₛ (n+2)` is a finite ordered product of `IsResourceGeneratorWires` gates (`hUniversal`)
— the resource set of *single-qubit unitaries, Bell-basis measurement, and four-qubit state
preparation* implements **every** evolution `E` of that register (`ResourceImplementsWires n
E`), for **every** `n`.

**Scope.** The statement ranges over every register `qubit ^⊗ₛ (n+2)` with at least two wires —
where the problem's content lives, since a `0`- or `1`-wire register needs no `CNOT` and its
universality is the single-qubit resource alone.
-/
theorem measurementResourceSetWires_realizes_of_universal (n : ℕ)
    (hUniversal : ∀ E : Evolution (qubit.tensorPow (n + 2)),
      ∃ L : List (Evolution (qubit.tensorPow (n + 2))),
        (∀ V ∈ L, IsResourceGeneratorWires n V) ∧ L.prod = E)
    (E : Evolution (qubit.tensorPow (n + 2))) : ResourceImplementsWires n E := sorry

end AxQM
