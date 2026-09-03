/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Tactic

/-!
# Classical trace distance between probability distributions (Nielsen & Chuang §9.1)

It is the classical quantity that the quantum trace distance `½ tr|ρ − σ|` (N&C `(9.11)`)
generalizes.

## Main definitions

* `classicalTraceDist` — the trace distance `½ ∑ₓ |pₓ − qₓ|` of `(9.1)`.

## Main statements

* `classicalTraceDist_deterministic_uniform` — **Exercise 9.1, part 1**: the
  trace distance between the deterministic distribution `(1, 0)` and the uniform
  distribution `(1/2, 1/2)` is `1/2`.
* `classicalTraceDist_ternary_example` — **Exercise 9.1, part 2**: the trace
  distance between `(1/2, 1/3, 1/6)` and `(3/4, 1/8, 1/8)` is `1/4`.
* `classicalTraceDist_binary` — **Exercise 9.2**: the trace distance between the
  two-outcome distributions `(p, 1 − p)` and `(q, 1 − q)` is `|p − q|`, for
  arbitrary real parameters `p` and `q`.
* `classicalTraceDist_isGreatest` — **Exercise 9.4**, N&C `(9.3)`:
  `D(p, q) = max_S |p(S) − q(S)|`, the maximum over all events `S` of the gap in
  the probability assigned to `S`.
* `classicalTraceDist_isGreatest_sub` (and its probability-distribution corollary
  `classicalTraceDist_isGreatest_sub_of_sum_eq_one`) — **Exercise 9.5**, N&C
  `(9.4)`: the absolute value signs may be removed, `D(p, q) = max_S (p(S) − q(S))`,
  because the optimal event `S⁺ = {x | pₓ ≥ qₓ}` already makes the gap nonnegative.
-/

namespace AxQM.Concrete

open scoped BigOperators

/-- The **classical trace distance** between two probability distributions
`p, q : ι → ℝ` over a finite index set, Nielsen & Chuang `(9.1)`:
`D(pₓ, qₓ) ≡ ½ ∑ₓ |pₓ − qₓ|`. Also known as the `L¹` or Kolmogorov distance. -/
noncomputable def classicalTraceDist {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  (∑ x, |p x - q x|) / 2

/-- **Nielsen & Chuang, Exercise 9.1 (part 1).** The trace distance between the
deterministic distribution `(1, 0)` and the uniform distribution `(1/2, 1/2)` is
`1/2`: `½(|1 − 1/2| + |0 − 1/2|) = ½(1/2 + 1/2) = 1/2`. -/
theorem classicalTraceDist_deterministic_uniform :
    classicalTraceDist ![1, 0] ![1 / 2, 1 / 2] = 1 / 2 := sorry

/-- **Nielsen & Chuang, Exercise 9.1 (part 2).** The trace distance between
`(1/2, 1/3, 1/6)` and `(3/4, 1/8, 1/8)` is `1/4`:
`½(|1/2 − 3/4| + |1/3 − 1/8| + |1/6 − 1/8|) = ½(1/4 + 5/24 + 1/24) = ½·(1/2) = 1/4`. -/
theorem classicalTraceDist_ternary_example :
    classicalTraceDist ![1 / 2, 1 / 3, 1 / 6] ![3 / 4, 1 / 8, 1 / 8] = 1 / 4 := sorry

/-- **Nielsen & Chuang, Exercise 9.2.** The trace distance between the two-outcome
distributions `(p, 1 − p)` and `(q, 1 − q)` is `|p − q|`, for arbitrary real
parameters `p q : ℝ`. The second summand collapses onto the first because the two
outcomes' deviations are equal and opposite:
`½(|p − q| + |(1 − p) − (1 − q)|) = ½(|p − q| + |q − p|) = ½(2|p − q|) = |p − q|`. -/
theorem classicalTraceDist_binary (p q : ℝ) :
    classicalTraceDist ![p, 1 - p] ![q, 1 - q] = |p - q| := sorry

/-- **Nielsen & Chuang, Exercise 9.4** — equation `(9.3)`. For two distributions `p, q : ι → ℝ` of
equal total mass (probability distributions in particular), the trace distance is the greatest
value of `|p(S) − q(S)|` over all events `S ⊆ {x}`: `D(p, q) = max_S |p(S) − q(S)| = max_S
|∑_{x∈S} pₓ − ∑_{x∈S} qₓ|`. `IsGreatest` packages both halves of `(9.3)`: `D(p, q)` is attained
(by the event where `p ≥ q`) and is an upper bound over all events. -/
theorem classicalTraceDist_isGreatest {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (h : ∑ x, p x = ∑ x, q x) :
    IsGreatest (Set.range fun S : Finset ι => |(∑ x ∈ S, p x) - (∑ x ∈ S, q x)|)
      (classicalTraceDist p q) := sorry

/-- **Nielsen & Chuang, Exercise 9.5** — equation `(9.4)`. The absolute value signs may be removed
from `(9.3)`: for two distributions `p, q : ι → ℝ` of equal total mass, the trace distance is
the greatest value of the *signed* gap `p(S) − q(S)` over all events `S ⊆ {x}`: `D(p, q) = max_S
(p(S) − q(S)) = max_S (∑_{x∈S} pₓ − ∑_{x∈S} qₓ)`. So the two maxima coincide. `IsGreatest`
packages both halves: `D(p, q)` is attained and is an upper bound, now over the signed gaps
rather than their absolute values. -/
theorem classicalTraceDist_isGreatest_sub {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (h : ∑ x, p x = ∑ x, q x) :
    IsGreatest (Set.range fun S : Finset ι => (∑ x ∈ S, p x) - (∑ x ∈ S, q x))
      (classicalTraceDist p q) := sorry

/-- **Nielsen & Chuang, Exercise 9.5** for probability distributions. -/
theorem classicalTraceDist_isGreatest_sub_of_sum_eq_one {ι : Type*} [Fintype ι]
    {p q : ι → ℝ} (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    IsGreatest (Set.range fun S : Finset ι => (∑ x ∈ S, p x) - (∑ x ∈ S, q x))
      (classicalTraceDist p q) := sorry

end AxQM.Concrete
