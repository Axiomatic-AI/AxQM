/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Evolution
import AxQM.Basic.API.MaximallyMixed
import AxQM.Basic.API.QuantumChannel

/-!
# AxQM.Basic.API — random-unitary (mixed-unitary) channels

A **random-unitary channel** (also *mixed-unitary channel*) is a quantum operation of the form
`E(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†` where the `Uₖ` are unitaries and `{pₖ}` is a probability distribution:
the channel applies a *randomly chosen* unitary `Uₖ` with probability `pₖ`. It is the running
object of **Nielsen & Chuang, Problem 8.3** (*Random unitary channels*), which asks whether every
unital channel — one with `E(I) = I` — is of this form: it holds for single qubits but *fails* for
larger systems.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A probability-weighted sum of density operators is a density operator:** if each `ρ i` is a
density operator and `p` is a probability distribution (`0 ≤ p i`, `∑ p i = 1`), then `∑ᵢ pᵢ ρᵢ`
is again a density operator. -/
theorem isDensityOp_sum_prob_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [Fintype ι]
    {ρ : ι → E →L[ℂ] E} (hρ : ∀ i, (ρ i).IsDensityOp)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, (p i : ℂ) • ρ i).IsDensityOp := by
  rw [ContinuousLinearMap.isDensityOp_iff]
  refine ⟨?_, ?_⟩
  · -- positivity: a finite sum of nonnegative multiples of positive operators is positive
    exact ContinuousLinearMap.isPositive_sum Finset.univ
      fun i _ => (hρ i).isPositive.smul_of_nonneg (by exact_mod_cast hp i)
  · -- trace: `tr (∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ · tr ρᵢ = ∑ᵢ pᵢ = 1`
    have h : (LinearMap.trace ℂ E) ↑(∑ i, (p i : ℂ) • ρ i) = ∑ i, (p i : ℂ) := by
      rw [ContinuousLinearMap.coe_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.coe_smul, map_smul, (hρ i).trace_eq_one, smul_eq_mul, mul_one]
    rw [h, ← Complex.ofReal_sum, hsum, Complex.ofReal_one]

/-- **A random-unitary (mixed-unitary) channel** of the system `S`:
a finite family of unitary `Evolution`s `unitary k` together with a probability distribution
`prob k` (nonnegative, summing to one). -/
structure RandomUnitaryChannel (S : QSystem) where
  /-- The number of unitaries in the mixture. -/
  card : ℕ
  /-- The probability weights `pₖ`. -/
  prob : Fin card → ℝ
  /-- The unitary evolutions `Uₖ` that are mixed over. -/
  unitary : Fin card → Evolution S
  /-- Each probability is nonnegative. -/
  prob_nonneg : ∀ i, 0 ≤ prob i
  /-- The probabilities sum to one. -/
  sum_prob : ∑ i, prob i = 1

namespace RandomUnitaryChannel

/-- **The action of a random-unitary channel** on a state: `E(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†`, the
probability-weighted mixture of the conjugated states `Uₖ ρ Uₖ† = (Uₖ).evolve ρ`. -/
def apply (C : RandomUnitaryChannel S) (ρ : State S) : State S where
  op := ∑ i, (C.prob i : ℂ) • ((C.unitary i).evolve ρ).op
  isDensity :=
    isDensityOp_sum_prob_smul (fun i => ((C.unitary i).evolve ρ).isDensity) C.prob_nonneg C.sum_prob

end RandomUnitaryChannel

/-- **A state-map (channel) `f` is unital** if it fixes the maximally mixed state `I/d`: `f (I/d) =
I/d`. For a **linear** channel this is Nielsen & Chuang's `E(I) = I` (the two differ by the
linear rescaling `I = d · (I/d)`). This is the fixed-point form of the unital channels of
Problem 8.3.

Note the predicate is stated on an arbitrary `f : State S → State S` — it captures only the
fixed point, not linearity/complete-positivity.
-/
def IsUnital [Nontrivial S.space] (f : State S → State S) : Prop :=
  f (maximallyMixedState S) = maximallyMixedState S

/-- **A state-map (channel) `f` is random-unitary (mixed-unitary)** if it agrees with the action of
some `RandomUnitaryChannel`, i.e. `f(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†` for a probability distribution `pₖ`
and unitaries `Uₖ`. This is the predicate in which **both** claims of Nielsen & Chuang, Problem
8.3 are phrased: for a *unital channel* `f`, is `f` random-unitary? — true for a qubit, false in
dimension `≥ 3`. -/
def IsRandomUnitary (f : State S → State S) : Prop :=
  ∃ C : RandomUnitaryChannel S, ∀ ρ, C.apply ρ = f ρ

end AxQM
