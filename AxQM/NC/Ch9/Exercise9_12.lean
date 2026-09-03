/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.GeneralizedDepolarizingChannel
import AxQM.Core.StrictContraction
import AxQM.NC.Ch9.Exercise9_6

/-!
# Nielsen & Chuang, Exercise 9.12 (The depolarizing channel is strictly contractive)

*(N&C p. 409.)*

For depolarizing channel, find D(E(rho),E(sigma)) via Bloch and prove strict contractivity.

* `qubitDepolarizingChannel`
* `qubitDepolarizingChannel_blochState_traceDistance`
* `qubitDepolarizingChannel_traceDistance`
* `qubitDepolarizingChannel_strictlyContractive`
-/

open Matrix

noncomputable section

namespace AxQM

/-- **The qubit depolarizing channel** `E(ρ) = p (I/2) + (1 − p) ρ` (Nielsen & Chuang eq. 8.100, the
depolarizing channel of §8.3.4). For `0 ≤ p ≤ 1` this is a genuine `State qubit → State qubit`
map. -/
def qubitDepolarizingChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : State qubit → State qubit :=
  genDepolarizingChannel 2 p hp0 hp1

/-- **The Bloch-explicit trace distance under the depolarizing channel** (Nielsen & Chuang Ex 9.12,
"find `D(E(ρ), E(σ))` using the Bloch representation"). For Bloch states with vectors `r⃗, s⃗`,
`D(E(ρ), E(σ)) = (1 − p) · ‖r⃗ − s⃗‖/2`. -/
theorem qubitDepolarizingChannel_blochState_traceDistance (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r s : Fin 3 → ℝ) (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1)
    (hs : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 ≤ 1) :
    (qubitDepolarizingChannel p hp0 hp1 (blochState r hr)).traceDistance
        (qubitDepolarizingChannel p hp0 hp1 (blochState s hs))
      = (1 - p) * (Real.sqrt ((r 0 - s 0) ^ 2 + (r 1 - s 1) ^ 2 + (r 2 - s 2) ^ 2) / 2) := sorry

/-- **Nielsen & Chuang, Exercise 9.12 (the trace distance under the depolarizing channel).** For
*arbitrary* qubit states `ρ` and `σ`, the depolarizing channel scales the trace distance by
exactly `1 − p`: `D(E(ρ), E(σ)) = (1 − p) D(ρ, σ)`. This is the closed form N&C asks us to
*find*. -/
theorem qubitDepolarizingChannel_traceDistance (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ σ : State qubit) :
    (qubitDepolarizingChannel p hp0 hp1 ρ).traceDistance (qubitDepolarizingChannel p hp0 hp1 σ)
      = (1 - p) * ρ.traceDistance σ := sorry

/-- **Nielsen & Chuang, Exercise 9.12 (strict contractivity).** For `0 < p ≤ 1` the depolarizing
channel `E(ρ) = p(I/2) + (1 − p)ρ` is *strictly contractive*: `D(E(ρ), E(σ)) < D(ρ, σ)` for
every pair of distinct states `ρ ≠ σ`.
-/
theorem qubitDepolarizingChannel_strictlyContractive (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : 0 < p) : StrictlyContractive (qubitDepolarizingChannel p hp0 hp1) := sorry

end AxQM
