/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_2
import AxQM.NC.Ch9.Exercise9_9
import AxQM.NC.Ch9.Exercise9_10
import AxQM.Basic.API.Mixture

/-!
# Nielsen & Chuang, Exercise 9.11 (mixing a fixed state: strictly contractive, unique fixed point)

*(N&C p. 408.)*

Show a quantum op mixing in fixed state rho_0 is strictly contractive, hence unique fixed point.

* `replaceMix_strictlyContractive` — the exercise's first clause: a channel mixing in a fixed state
  is `AxQM.StrictlyContractive`.
* `replaceMix_existsUnique_fixedPoint` — the exercise's second clause, the unique fixed point `∃! ρ,
  E ρ = ρ`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.11 — a channel mixing in a fixed state is strictly contractive.**
If `E′` is a channel and `E τ = p ρ₀ + (1 − p) E′(τ)` with `0 < p ≤ 1` (N&C `(9.52)`), then `E`
satisfies `AxQM.StrictlyContractive` — it strictly decreases the trace distance between
any two *distinct* states. -/
theorem replaceMix_strictlyContractive {E E' : State S → State S} {ρ₀ : State S} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hE' : IsChannel E')
    (hE : ∀ τ, E τ = State.mixPair hp0.le hp1 ρ₀ (E' τ)) :
    StrictlyContractive E := sorry

/-- **N&C Exercise 9.11 — a channel mixing in a fixed state has a unique fixed point.** If `E` is a
channel with `E τ = p ρ₀ + (1 − p) E′(τ)` for a channel `E′` and `0 < p ≤ 1` (N&C `(9.52)`),
then `E` has a *unique* fixed point: `∃! ρ, E ρ = ρ`. This is the exercise's second clause,
"…and thus has a unique fixed point".

The channel hypothesis `hE` on `E` is exactly N&C's opening "Suppose `E` is a trace-preserving
quantum operation…"; `[Nonempty (State S)]` records that `S` is a genuine quantum system, so
"a fixed **state** exists" is non-vacuous.
-/
theorem replaceMix_existsUnique_fixedPoint [Nonempty (State S)] {E E' : State S → State S}
    {ρ₀ : State S} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hE : IsChannel E) (hE' : IsChannel E')
    (hmix : ∀ τ, E τ = State.mixPair hp0.le hp1 ρ₀ (E' τ)) :
    ∃! ρ : State S, E ρ = ρ := sorry

end AxQM
