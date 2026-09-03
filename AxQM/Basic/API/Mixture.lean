/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.TraceDistance
import AxQM.Basic.API.RandomUnitaryChannel
import AxQM.Basic.SystemIso
import AxQM.Basic.API.Evolution
import AxQM.Basic.Composite

/-!
# AxQM.Basic.API — probabilistic mixtures of states

Nielsen & Chuang repeatedly form the **probabilistic mixture** `∑ᵢ pᵢ ρᵢ` of a family of
states `{ρᵢ}` weighted by a probability distribution `{pᵢ}` — the density operator describing
"prepare `ρᵢ` with probability `pᵢ`" (e.g. the mixtures of Theorem 9.3, the joint convexity
`(9.50)`, and the convexity exercises 9.8–9.13). This file defines that mixture as a `State`.

## Main definitions

* `State.mix` — the mixed state `∑ᵢ pᵢ ρᵢ` (N&C mixtures).
* `State.mixPair` — the two-outcome case `p ρ + (1 − p) σ`.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The **probabilistic mixture** `∑ᵢ pᵢ ρᵢ` of a finite family of states `ρ : ι → State S` weighted
by a probability distribution `p : ι → ℝ` (`0 ≤ pᵢ` and `∑ᵢ pᵢ = 1`): the state whose density
operator is the convex combination `∑ᵢ (pᵢ : ℂ) • ρᵢ.op`.
-/
noncomputable def State.mix {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (ρ : ι → State S) : State S where
  op := ∑ i, (p i : ℂ) • (ρ i).op
  isDensity := isDensityOp_sum_prob_smul (fun i => (ρ i).isDensity) hp hsum

/-- The **binary probabilistic mixture** `p ρ + (1 − p) σ` of two states, weighted by a single
probability `p ∈ [0, 1]`: the state whose density operator is the convex combination
`(p : ℂ) • ρ.op + (1 − p : ℂ) • σ.op`. The two-outcome special case of `State.mix` — "prepare `ρ`
with probability `p`, else `σ`" — which N&C's channel-mixing exercises repeatedly form: the mixing
operation `E(ρ) = p ρ₀ + (1 − p) E'(ρ)` of Exercise 9.11, the depolarizing channel
`p I/2 + (1−p) ρ`, and the bit-flip channel. -/
noncomputable def State.mixPair {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ σ : State S) : State S where
  op := (p : ℂ) • ρ.op + ((1 - p : ℝ) : ℂ) • σ.op
  isDensity :=
    ρ.isDensity.convex_combination σ.isDensity (Complex.zero_le_real.mpr hp0)
      (Complex.zero_le_real.mpr (by linarith : (0 : ℝ) ≤ 1 - p)) (by push_cast; ring)

end AxQM
