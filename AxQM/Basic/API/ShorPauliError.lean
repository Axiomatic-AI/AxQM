/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorCodeProjector

/-!
# AxQM.Basic.API — single-qubit Pauli errors on the nine-qubit Shor register

Infrastructure for the **error set** of Nielsen & Chuang's Exercise 10.10: the
identity `I` together with the single-qubit Pauli errors `X_j, Y_j, Z_j` for `j = 1..9` on the
nine-qubit Shor register `shorReg = bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)`. This file builds those
errors.

## Contents

* `blockSinglePauli A pos` / `shorSinglePauli A block pos` — a single-qubit observable `A` placed at
  position `pos` inside a block, and at qubit `(block, pos)` of the whole register, via nested
  `Observable.tmul` with `Observable.id` on the untouched factors.
* `pauliErrorObs` (`0 ↦ X`, `1 ↦ Y`, `2 ↦ Z`) and `shorPauliError t block pos` — the single-qubit
  Pauli error **operators** `{X_j, Y_j, Z_j}`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **A single-qubit observable `A` placed at position `pos` of a three-qubit block**
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`: `A` on the `pos`-th qubit, the identity on the other two.
`pos = 0 ↦ A ⊗ I ⊗ I`, `pos = 1 ↦ I ⊗ A ⊗ I`, `pos = 2 ↦ I ⊗ I ⊗ A`. -/
def blockSinglePauli (A : Observable qubit) (pos : Fin 3) : Observable bitFlipReg :=
  match pos with
  | 0 => A ⊗ (Observable.id qubit ⊗ Observable.id qubit)
  | 1 => Observable.id qubit ⊗ (A ⊗ Observable.id qubit)
  | 2 => Observable.id qubit ⊗ (Observable.id qubit ⊗ A)

/-- **A single-qubit observable `A` placed at qubit `(block, pos)` of the nine-qubit register**
`shorReg = bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)`: `blockSinglePauli A pos` on the `block`-th cat
block, the identity on the other two blocks. -/
def shorSinglePauli (A : Observable qubit) (block pos : Fin 3) : Observable shorReg :=
  match block with
  | 0 => blockSinglePauli A pos ⊗ (Observable.id bitFlipReg ⊗ Observable.id bitFlipReg)
  | 1 => Observable.id bitFlipReg ⊗ (blockSinglePauli A pos ⊗ Observable.id bitFlipReg)
  | 2 => Observable.id bitFlipReg ⊗ (Observable.id bitFlipReg ⊗ blockSinglePauli A pos)

/-- **The three single-qubit Pauli error observables indexed by `Fin 3`:** `0 ↦ X`, `1 ↦ Y`, `2 ↦
Z`. The three non-identity single-qubit errors, used to enumerate the Shor error family `{X_j,
Y_j, Z_j}`. -/
def pauliErrorObs : Fin 3 → Observable qubit :=
  ![pauliXObservable, pauliYObservable, pauliZObservable]

/-- **The single-qubit Pauli error operators** `{X_j, Y_j, Z_j}` of the Shor code, as operators on
the register state space: `shorPauliError t block pos` is the Pauli of type `t` (`0 = X`, `1 = Y`,
`2 = Z`) acting on qubit `(block, pos)`, the identity elsewhere — the operation elements the quantum
error-correction conditions are checked against. -/
def shorPauliError (t block pos : Fin 3) : shorReg.space →L[ℂ] shorReg.space :=
  (shorSinglePauli (pauliErrorObs t) block pos).op

end AxQM
