/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.MeasureObservable

/-!
# AxQM.Basic.API — collapse into the `±1` eigenspaces of an involution observable

The constructions behind **Nielsen & Chuang, Exercise 5.9**: for a unitary `U`
with eigenvalues `±1` (a self-adjoint involution, `U² = I`), the phase-estimation circuit of
Exercise 4.34 (`measureObservableCircuit U = (H ⊗ 1) · C(U) · (H ⊗ 1)`) collapses an arbitrary input
`|ψ⟩` into one of the two eigenspaces of `U`, with the single ancilla qubit as the classical
indicator of which eigenspace. This file supplies the pieces that Exercise 4.34 did not need — the
`−1`-outcome collapse state, and the fact that *both* collapsed states are genuine `±1` eigenstates
of `U`.

## Main declarations
* `Observable.postMeasMinus` — the **normalized `−1` post-measurement pure state**
  `P₋|ψ⟩ / ‖P₋|ψ⟩‖`,
  the collapsed target when the `±1` measurement of `A` yields `−1`. The exact `−1` sibling of the
  existing `Observable.postMeasPlus`, with `postMeasurement_signMeasurement_minus` (the
  collapse to `postMeasMinus`).
* `Observable.postMeasPlus_hasEigenstate` / `Observable.postMeasMinus_hasEigenstate` — **the
  collapse lands in the eigenspace:** the `+1` (resp. `−1`) collapsed state is a genuine `+1` (resp.
  `−1`) eigenstate of `A`, `A |ψ'⟩ = ±|ψ'⟩`. This is the content Exercise 5.9 emphasises over 4.34:
  the post-measurement state is *the corresponding eigenvector*.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Observable

/-- The **normalized `−1` post-measurement pure state** `P₋|ψ⟩ / ‖P₋|ψ⟩‖` — the collapsed state
after the `±1` measurement of `A` yields `−1`, defined when `P₋|ψ⟩ ≠ 0` (i.e. when `−1`
is a possible outcome). It is the `−1` eigenstate of `A`. The `−1` sibling of
`Observable.postMeasPlus`. -/
def postMeasMinus (A : Observable S) (ψ : PureState S) (hne : A.projMinus ψ.vec ≠ 0) :
    PureState S :=
  PureState.normalize (A.projMinus ψ.vec) hne

/-- **State update, `−1` outcome.** When the `±1` measurement of `A` on `|ψ⟩` yields
`−1`, the system collapses to the normalized state `P₋|ψ⟩ / ‖P₋|ψ⟩‖ = postMeasMinus`. -/
theorem postMeasurement_signMeasurement_minus (A : Observable S) (hinv : A.op * A.op = 1)
    (ψ : PureState S) (hne : A.projMinus ψ.vec ≠ 0)
    (hp : (A.signMeasurement hinv).bornProb ψ.toState 1 ≠ 0) :
    (A.signMeasurement hinv).postMeasurement ψ.toState 1 hp = (A.postMeasMinus ψ hne).toState :=
      sorry

/-- **The `+1` collapse is a `+1` eigenstate.** For a `±1` observable `A` (`A² = I`), the
post-measurement state `postMeasPlus = P₊|ψ⟩/‖P₊|ψ⟩‖` is a genuine `+1` eigenstate of `A`: `A
|ψ'⟩ = |ψ'⟩`. This is Exercise 5.9's "the post-measurement state is the corresponding
eigenvector", `+1` case. -/
theorem postMeasPlus_hasEigenstate (A : Observable S) (hinv : A.op * A.op = 1) (ψ : PureState S)
    (hne : A.projPlus ψ.vec ≠ 0) :
    A.HasEigenstate 1 (A.postMeasPlus ψ hne) := sorry

/-- **The `−1` collapse is a `−1` eigenstate.** For a `±1` observable `A` (`A² = I`), the
post-measurement state `postMeasMinus = P₋|ψ⟩/‖P₋|ψ⟩‖` is a genuine `−1` eigenstate of `A`: `A
|ψ'⟩ = −|ψ'⟩`. This is Exercise 5.9's "post-measurement state is the corresponding eigenvector",
`−1` case. -/
theorem postMeasMinus_hasEigenstate (A : Observable S) (hinv : A.op * A.op = 1) (ψ : PureState S)
    (hne : A.projMinus ψ.vec ≠ 0) :
    A.HasEigenstate (-1) (A.postMeasMinus ψ hne) := sorry

end Observable

end AxQM
