/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlBranchExt
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ControlledZ

/-!
# The Barenco no-work-qubit reduction for multiply-controlled gates (Nielsen & Chuang §4.3)

Nielsen & Chuang's Figure 4.8 builds the *doubly*-controlled gate `C²(V²)` from single-qubit
controlled `V`, `V†` and two `CNOT`s. Exercise 4.28 asks for the analogous
construction of an `n`-control gate `Cⁿ(V²)` **using no work qubits**.

## Main declarations
* `qtower n S` — the register `qubitⁿ ⊗ S`: `n` control qubits wrapping an inner system `S`.
* `mcCtrl n E` / `unCtrl n E` — `E : Evolution S` wrapped by `n` outer control qubits, **either**
  each *controlling* `E` (`mcCtrl`, so `E` fires iff all `n` controls are `|1⟩` — the `Cⁿ`
  multiplexer) **or** each *idle* (`unCtrl`, so `E` fires unconditionally).
* `qtower_qubit_comm` — the register reassociation `qtower m (qubit ⊗ S) = qtower (m+1) S`.
* `barencoReductionCircuit k Vg` — the right-hand side of the reduction on
  `qtower k (qubit ⊗ M)` (inner = control ⊗ target-module `M`, `Vg : Evolution M`): the ordered
  composition `Cᵏ(V) · Cᵏ(X) · C(V†) · Cᵏ(X) · C(V)`.
* `barencoTail k Vg` — the multiplexer-free tail `Cᵏ(X) · C(V†) · Cᵏ(X) · C(V)` of one layer.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S M : QSystem}

/-- **The control register** `qtower n S = qubitⁿ ⊗ S`: `n` control qubits (added on the left, one
at a time) wrapping an inner system `S`. -/
def qtower : ℕ → QSystem → QSystem
  | 0, S => S
  | (n + 1), S => qubit ⊗ qtower n S

/-- **The `n`-controlled multiplexer** `mcCtrl n E = Cⁿ(E)`. Built by iterating the single control
`controlledUnitary`; `mcCtrl 0 E = E` and `mcCtrl (n+1) E = C(mcCtrl n E)`. -/
def mcCtrl : (n : ℕ) → Evolution S → Evolution (qtower n S)
  | 0, E => E
  | (n + 1), E => controlledUnitary (mcCtrl n E)

/-- **The idle wrapping** `unCtrl n E`. Built by iterating the idle wrap `Evolution.onRight`;
`unCtrl 0 E = E` and `unCtrl (n+1) E` wraps `unCtrl n E` with an idle qubit. -/
def unCtrl : (n : ℕ) → Evolution S → Evolution (qtower n S)
  | 0, E => E
  | (n + 1), E => (unCtrl n E).onRight qubit

/-- **Pushing a control from the target into the tower.** `qtower m (qubit ⊗ S) = qtower (m+1) S`:
both are the right-nested tower of `m + 1` control qubits over `S`. -/
theorem qtower_qubit_comm (m : ℕ) (S : QSystem) :
    qtower m (qubit ⊗ S) = qtower (m + 1) S := by
  induction m with
  | zero => rfl
  | succ k ih => exact congrArg (qubit ⊗ ·) ih

/-- **The Figure-4.8 reduction circuit** for `Cᵏ⁺¹(V²)` on `qtower k (qubit ⊗ M)` (inner = innermost
control ⊗ target-module `M`, with `Vg : Evolution M`). Reading right to left (the rightmost acts
first), the five gates are: `C(V)` on the inner control; `Cᵏ(X)` on the outer `k` controls
targeting the inner control (`pauliXGate.onLeft M`); `C(V†)` on the inner control; `Cᵏ(X)`
again; and `Cᵏ(V)` on the outer `k` controls targeting the target-module, skipping the inner
control (`Vg.onRight qubit`). -/
def barencoReductionCircuit (k : ℕ) (Vg : Evolution M) : Evolution (qtower k (qubit ⊗ M)) :=
  (mcCtrl k (Vg.onRight qubit)).comp
    ((mcCtrl k (pauliXGate.onLeft M)).comp
      ((unCtrl k (controlledUnitary Vg.adjoint)).comp
        ((mcCtrl k (pauliXGate.onLeft M)).comp
          (unCtrl k (controlledUnitary Vg)))))

/-- **The tail of one Barenco reduction layer** on `qtower k (qubit ⊗ M)`: everything of
`barencoReductionCircuit k Vg` *after* the leading `Cᵏ(V)` multiplexer, i.e.
`Cᵏ(X) · C(V†) · Cᵏ(X) · C(V)` — two multiply-controlled `NOT`s (`mcCtrl k (pauliXGate.onLeft M)`)
and the two idle single-qubit-controlled gates `C(V†)`, `C(V)`
(`unCtrl k (controlledUnitary …)`). -/
def barencoTail (k : ℕ) (Vg : Evolution M) : Evolution (qtower k (qubit ⊗ M)) :=
  (mcCtrl k (pauliXGate.onLeft M)).comp
    ((unCtrl k (controlledUnitary Vg.adjoint)).comp
      ((mcCtrl k (pauliXGate.onLeft M)).comp
        (unCtrl k (controlledUnitary Vg))))

end AxQM
