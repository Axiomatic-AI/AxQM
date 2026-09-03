/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliMeasurement
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.PhaseFlipCode

/-!
# AxQM.Basic.API — the B92 protocol apparatus (Nielsen & Chuang §12.6.3)

Model of the B92 quantum-key-distribution protocol (N&C pp. 588–591): Alice's non-orthogonal
signal states, Bob's two measurement bases, his projective sign measurement, and the resulting
Born probability of the outcome `b = 1`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Alice's state `|ψ_a⟩`** as a function of her classical bit `a` (`false ↔ 0`, `true ↔ 1`). The
two non-orthogonal states of the B92 protocol. -/
def b92AliceState (a : Bool) : PureState qubit := cond a qubitPlus qubitKet0

/-- **Bob's `±1` observable** as a function of his basis-choice bit `a'` (`false ↔ 0`, `true ↔ 1`):
the Pauli `Z` observable (measuring in the computational basis `{|0⟩, |1⟩}`) if `a' = 0`, the Pauli
`X` observable (measuring in the `{|+⟩, |-⟩}` basis) if `a' = 1`. -/
def b92BobObservable (a' : Bool) : Observable qubit := cond a' pauliXObservable pauliZObservable

/-- **Bob's measurement** for basis choice `a'`: the sign measurement of `b92BobObservable a'`. -/
def b92Measurement (a' : Bool) : Measurement (Fin 2) qubit :=
  (b92BobObservable a').signMeasurement <| by
    cases a'
    · exact pauliZObservable_op_mul_self
    · exact pauliXObservable_op_mul_self

/-- **The Born probability `P(b = 1 | a, a')`** of Bob obtaining outcome `b = 1` (the `−1`
eigenstate, `Fin 2` index `1`) when Alice sends `|ψ_a⟩` and Bob measures in basis `a'`. -/
def b92ProbB1 (a a' : Bool) : ℝ := (b92Measurement a').bornProb (b92AliceState a).toState 1

end AxQM
