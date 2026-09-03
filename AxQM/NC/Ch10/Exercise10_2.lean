/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Exercise9_13
import AxQM.Basic.API.PauliMeasurement
import AxQM.Basic.API.Mixture
import AxQM.Basic.API.UnreadMeasurement
import AxQM.Basic.API.NMRSwap
import AxQM.Basic.API.NMRGroverOracle
import AxQM.Basic.API.BlochRotationGate

/-!
# Nielsen & Chuang, Exercise 10.2 (Alternate operator-sum representation of the bit flip channel)

*(N&C p. 429.)*

Bit flip channel (1-p)rho+pXrhoX has alternate operator-sum rep (1-2p)rho+2pP+rhoP+ +2pP-rhoP-.

* `bitFlipMeasurementModel` — the leave-alone/measure model: with probability `1 − 2p` the qubit is
  left alone, with probability `2p` it is measured in the `X`-eigenbasis and the outcome discarded.
* `bitFlipChannel_eq_measurementModel` — the exercise's identity: the bit flip channel equals the
  leave-alone/measure model, `bitFlipChannel (1 − p) = bitFlipMeasurementModel p`, for `0 ≤ p ≤
  1/2`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The alternate operator-sum representation of the bit flip channel, as N&C's physical model**
(Nielsen & Chuang, Exercise 10.2): with probability `1 − 2p` the qubit is left alone, and with
probability `2p` it is measured in the `X`-eigenbasis `|±⟩` and the outcome discarded. Formally
the binary mixture `State.mixPair (1 − 2p) ρ (E)` of the input `ρ` (weight `1 − 2p`) with the
unread projective `X`-measurement `E = (signMeasurement pauliXObservable).unreadState ρ` (weight
`2p`), whose operator is `P₊ρP₊ + P₋ρP₋`. Requires `0 ≤ p ≤ 1/2` so that `1 − 2p` is a valid
mixing weight. -/
noncomputable def bitFlipMeasurementModel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    State qubit → State qubit :=
  fun ρ =>
    State.mixPair (p := 1 - 2 * p) (by linarith) (by linarith) ρ
      ((pauliXObservable.signMeasurement pauliXObservable_op_mul_self).unreadState ρ)

/-- **Nielsen & Chuang, Exercise 10.2 — the bit flip channel's alternate operator-sum
representation.** For `0 ≤ p ≤ 1/2`, the bit flip channel `E(ρ) = (1 − p)ρ + pXρX`
(`bitFlipChannel (1 − p)`) equals the leave-alone/measure model `bitFlipMeasurementModel p`,
whose operator is `(1 − 2p)ρ + 2p P₊ρP₊ + 2p P₋ρP₋`. This is the identity the exercise asks for:
the channel admits the alternate operator-sum representation in the `X`-eigenbasis. -/
theorem bitFlipChannel_eq_measurementModel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    bitFlipChannel (1 - p) (by linarith) (by linarith) = bitFlipMeasurementModel p hp0 hp1 := sorry

end AxQM
