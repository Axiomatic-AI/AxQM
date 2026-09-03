/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.GeneralizedDepolarizingChannel
import AxQM.Basic.API.TracePow
import AxQM.ToMathlib.Analysis.InnerProductSpace.Density
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.Mul

/-!
# Nielsen & Chuang, Exercise 8.18 (Trace powers are non-increasing under depolarization)

*(N&C p. 379.)*

For k≥1 show tr(ρ^k) is never increased by the depolarizing channel.

* `traceOfPow_genDepolarizingChannel_le`
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 8.18.** For `k ≥ 1` the depolarizing channel never increases the
`k`-th trace power `tr(ρᵏ)`.
-/
theorem traceOfPow_genDepolarizingChannel_le {d : ℕ} [NeZero d] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : State (qudit d)) {k : ℕ} (hk : 1 ≤ k) :
    (genDepolarizingChannel d p hp0 hp1 ρ).traceOfPow k ≤ ρ.traceOfPow k := sorry

end AxQM
