/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch8.Problem8_3
import AxQM.NC.Ch9.Theorem9_2
import AxQM.Core.StrictContraction

/-!
# Nielsen & Chuang, Exercise 9.13 (Bit flip channel: contractive, not strictly; fixed points)

*(N&C p. 409.)*

Show bit flip channel is contractive not strictly; find its fixed points.

* `bitFlipProb_nonneg`
* `bitFlipProb_sum`
* `bitFlipChannel`
* `bitFlipChannel_traceDistance_le` — contractive: `D(E(ρ), E(σ)) ≤ D(ρ, σ)` for all `ρ, σ`.
* `bitFlipChannel_isFixedPt_blochState_iff` — for `p < 1`, a Bloch state is a fixed point *iff*
  `r_y = r_z = 0`.
* `not_strictlyContractive_bitFlipChannel` — not strictly contractive: `¬ StrictlyContractive E`.
-/

open Matrix

noncomputable section

namespace AxQM

/-- The bit flip weights `![p, 1 − p, 0, 0]` form a **nonnegative** family, given `0 ≤ p ≤ 1`. -/
theorem bitFlipProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ i, 0 ≤ (![p, 1 - p, 0, 0] : Fin 4 → ℝ) i := by
  intro i
  fin_cases i <;> simp <;> linarith

/-- The bit flip weights `![p, 1 − p, 0, 0]` **sum to one**: `p + (1 − p) + 0 + 0 = 1`. -/
theorem bitFlipProb_sum (p : ℝ) : ∑ i, (![p, 1 - p, 0, 0] : Fin 4 → ℝ) i = 1 := by
  simp [Fin.sum_univ_four]

/-- **The bit flip channel** `E(ρ) = p ρ + (1 − p) X ρ X` (Nielsen & Chuang §8.3.3, eq. `(8.94)`),
for flip probability `1 − p`, `0 ≤ p ≤ 1`. Realised as the qubit Pauli channel
(`AxQM.pauliChannel`, Problem 8.3) with weight distribution `![p, 1 − p, 0, 0]` over the
Paulis `I, X, Y, Z` — mixing `I` (weight `p`) and `X` (weight `1 − p`) only. -/
def bitFlipChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : State qubit → State qubit :=
  (pauliChannel ![p, 1 - p, 0, 0] (bitFlipProb_nonneg hp0 hp1) (bitFlipProb_sum p)).apply

/-- **The bit flip channel is contractive** (Nielsen & Chuang, Exercise 9.13, part 1): it never
increases the trace distance, `D(E(ρ), E(σ)) ≤ D(ρ, σ)`. -/
theorem bitFlipChannel_traceDistance_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ σ : State qubit) :
    (bitFlipChannel p hp0 hp1 ρ).traceDistance (bitFlipChannel p hp0 hp1 σ)
      ≤ ρ.traceDistance σ := sorry

/-- **The fixed points of the bit flip channel are exactly the `x̂`-axis states** (Nielsen & Chuang,
Exercise 9.13, "find the set of fixed points"), for the generic channel `p < 1`.

(At `p = 1` the channel is the identity and every state is fixed, so the hypothesis `p < 1` is
necessary.)
-/
theorem bitFlipChannel_isFixedPt_blochState_iff (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp1' : p < 1)
    {r : Fin 3 → ℝ} (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    Function.IsFixedPt (bitFlipChannel p hp0 hp1) (blochState r h) ↔ r 1 = 0 ∧ r 2 = 0 := sorry

/-- **The bit flip channel is *not* strictly contractive** (Nielsen & Chuang, Exercise 9.13,
part 2). Strict contraction (`StrictlyContractive`, Exercise 9.10) would give
`D(E(ρ), E(σ)) < D(ρ, σ)` for *every* pair of distinct states; the bit flip channel is strictly
contractive for no value of `p`. -/
theorem not_strictlyContractive_bitFlipChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ¬ StrictlyContractive (bitFlipChannel p hp0 hp1) := sorry

end AxQM
