/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ClassicalQueryModel
import AxQM.Concrete.ClassicalCountingIntervals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Concrete: any classical counting algorithm needs `Ω(N)` oracle calls (N&C Exercise 6.14)

Nielsen & Chuang, Exercise 6.14 (p. 262).
-/

open MeasureTheory

namespace AxQM.Concrete

/-- A **randomized classical counting algorithm** on a Boolean oracle over `Fin N`: a probability
distribution over deterministic adaptive decision trees, each making at most `budget` oracle calls.
This is the standard, fully general model of a classical algorithm consulting the oracle: the
internal randomness is an arbitrary probability space `(Ω, μ)`, and running the tree selected by the
randomness against an oracle `f` yields the estimate `(alg ω).eval f`. The measurability field makes
each such estimate a genuine random variable, so its success probability is well-defined. -/
structure RandomizedCountingAlgorithm (N : ℕ) where
  /-- The sample space of the algorithm's internal randomness. -/
  Ω : Type*
  /-- The measurable-space structure on the randomness. -/
  mΩ : MeasurableSpace Ω
  /-- The distribution over the randomness. -/
  μ : @MeasureTheory.Measure Ω mΩ
  /-- `μ` is a probability measure. -/
  isProb : @MeasureTheory.IsProbabilityMeasure Ω mΩ μ
  /-- The worst-case number of oracle calls (query budget). -/
  budget : ℕ
  /-- The deterministic decision tree run for each value of the randomness. -/
  alg : Ω → QueryTree N
  /-- Every realised tree makes at most `budget` oracle calls. -/
  depth_le : ∀ ω, (alg ω).depth ≤ budget
  /-- For every oracle, the algorithm's output is a measurable function of the randomness, so the
  probability of any accuracy event is well-defined. -/
  measurable_eval : ∀ f : Fin N → Bool, Measurable[mΩ] (fun ω => (alg ω).eval f)

/-- **Exercise 6.14 (Nielsen & Chuang), `Ω(N)` form.** For each accuracy constant `c ≥ 0` there is a
positive constant `a` (depending only on `c`) such that any randomized classical counting algorithm
correct to accuracy `c √M` with probability `≥ 3/4` for every oracle makes `a · N ≤ budget` oracle
calls, once `2 (⌈c²⌉₊ + 1) ≤ N`. This is the statement that any such algorithm makes `Ω(N)` oracle
calls. -/
theorem counting_query_needs_linear_oracle_calls {c : ℝ} (hc : 0 ≤ c) :
    ∃ a : ℝ, 0 < a ∧ ∀ (N : ℕ) (A : RandomizedCountingAlgorithm N),
      2 * (⌈c ^ 2⌉₊ + 1) ≤ N →
      (∀ f : Fin N → Bool,
        3 / 4 ≤ A.μ.real {ω | |(A.alg ω).eval f - (numSolutions f : ℝ)|
          ≤ c * Real.sqrt (numSolutions f)}) →
      a * N ≤ A.budget := sorry

end AxQM.Concrete
