/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import AxQM.ToMathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Shannon entropy of a discrete distribution

For a finite type `ι` and a function `p : ι → ℝ` (interpreted as a probability mass function
when `p i ∈ [0, 1]` and `∑ i, p i = 1`), the **Shannon entropy** of `p` is
`H(p) = −∑ᵢ pᵢ log pᵢ` (in nats).

## Main definitions

- `Real.entropy : (ι → ℝ) → ℝ`

## Main results

- `Real.entropy_eq` (rfl-lemma exposing the sum form).
- `Real.entropy_prod`: product additivity for an independent joint distribution.
- `Real.entropy_eq_log_card_iff`: **equality condition** (Nielsen–Chuang Theorem 11.2) — the
  bound `log (card ι)` is attained iff `p` is the uniform distribution.
- `Real.entropy_le_cross_entropy_of_sum_le`: **sub-normalized cross-entropy bound**, the shared
  kernel — entropy is at most cross-entropy when `p`'s support lies in `q`'s and `∑ q ≤ ∑ p`.
- `Real.entropy_le_cross_entropy_of_support_subset`: **Gibbs' inequality, support-aware
  form** — the equal-mass (`∑ p = ∑ q`) corollary of `entropy_le_cross_entropy_of_sum_le`.
- `Real.relativeEntropy_eq_zero_iff`: **equality condition** — `D(p‖q) = 0 ↔ p = q` under the
  same support/absolute-continuity hypothesis (`q x = 0 → p x = 0`, equal total mass). With the
  support-aware nonneg result this is the faithful real-valued rendering of Nielsen–Chuang
  Theorem 11.1 ("non-negative, with equality iff `p = q`") on the domain where `relativeEntropy`
  equals N&C's `H(p‖q)`.
-/

@[expose] public section

namespace Real

variable {ι : Type*} [Fintype ι]

/-- The Shannon entropy (in nats) of a discrete distribution `p : ι → ℝ`. -/
noncomputable def entropy (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

theorem entropy_eq (p : ι → ℝ) : entropy p = ∑ i, Real.negMulLog (p i) := rfl

/-- The **classical relative entropy** (Kullback–Leibler divergence) of `p` with respect to
`q`: `D(p‖q) = ∑ x, p x * (log (p x) - log (q x))`. With Mathlib's junk-value
`Real.log 0 = 0`, boundary terms vanish where `p x = 0`; nonnegativity holds under
`∑ p = ∑ q = 1` and absolute continuity. -/
noncomputable def relativeEntropy (p q : ι → ℝ) : ℝ :=
  ∑ x, p x * (Real.log (p x) - Real.log (q x))

variable {κ : Type*} [Fintype κ]

/-- **Product additivity**: the Shannon entropy of an independent joint distribution
`r (i, j) := p i * q j` is the sum of the marginal entropies, provided both marginals sum
to one. -/
theorem entropy_prod {p : ι → ℝ} {q : κ → ℝ} (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) :
    entropy (fun ij : ι × κ ↦ p ij.1 * q ij.2) = entropy p + entropy q := by
  rw [entropy_eq, Fintype.sum_prod_type, entropy_eq, entropy_eq]
  calc ∑ x, ∑ y, negMulLog (p x * q y)
      = ∑ x, ∑ y, (q y * negMulLog (p x) + p x * negMulLog (q y)) := by simp_rw [negMulLog_mul]
    _ = ∑ x, ((∑ y, q y) * negMulLog (p x) + p x * ∑ y, negMulLog (q y)) := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ x, negMulLog (p x) + (∑ x, p x) * ∑ y, negMulLog (q y) := by
        rw [hq]; simp [Finset.sum_add_distrib, Finset.sum_mul]
    _ = ∑ x, negMulLog (p x) + ∑ y, negMulLog (q y) := by rw [hp, one_mul]

/-- **Product-distribution entropy additivity** (per-coordinate form): for a family of probability
distributions `r j : ι → ℝ` (each `∑ₓ r j x = 1`), the Shannon entropy of the product
distribution `y ↦ ∏ⱼ r j (y j)` over `Fin n → ι` is the sum `∑ⱼ H(r j)` of the coordinate
entropies.

The i.i.d. tensor power `entropy_pi_prod_of_sum_eq_one` (`H(p^{⊗n}) = n · H(p)`) is the special
case `r j = p`. It is the "noise entropy single-letterizes" ingredient in the converse of
Shannon's noisy channel coding theorem: the conditional output entropy `H(Yⁿ | Xⁿ = xⁿ) = H(∏ⱼ
q(·|xⱼ))` of the memoryless `n`-use channel splits as `∑ⱼ H(q(·|xⱼ))`.
-/
theorem entropy_pi_prod :
    ∀ {n : ℕ} {r : Fin n → ι → ℝ}, (∀ j, ∑ x, r j x = 1) →
      entropy (fun y : Fin n → ι ↦ ∏ j, r j (y j)) = ∑ j, entropy (r j) := by
  intro n
  induction n with
  | zero =>
      intro r _
      rw [Fin.sum_univ_zero, entropy_eq]
      refine Finset.sum_eq_zero fun y _ ↦ ?_
      simp [Real.negMulLog_one]
  | succ n ih =>
      intro r hr
      -- The outer marginal (product over the first `n` coordinates) is a probability distribution.
      have hout_sum : ∑ z : Fin n → ι, ∏ i, r i.castSucc (z i) = 1 := by
        rw [← Fintype.piFinset_univ, Finset.sum_prod_piFinset]
        simp [hr]
      -- Bridge `Fin (n+1) → ι ≃ (Fin n → ι) × ι` (peel the last coordinate).
      have hbij : entropy (fun y : Fin (n + 1) → ι ↦ ∏ j, r j (y j))
          = entropy (fun pair : (Fin n → ι) × ι ↦
              (∏ i, r i.castSucc (pair.1 i)) * r (Fin.last n) pair.2) := by
        rw [entropy_eq, entropy_eq, ← (Fin.succFunEquiv ι n).sum_comp]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        simp only [Fin.succFunEquiv_apply, Fin.prod_univ_castSucc]
        rfl
      rw [hbij, entropy_prod hout_sum (hr (Fin.last n)),
        ih (r := fun i ↦ r i.castSucc) (fun i ↦ hr i.castSucc), Fin.sum_univ_castSucc]

/-- **Pi-tensor-power additivity**: the Shannon entropy of the n-fold independent
product distribution `κ ↦ ∏ i, p (κ i)` over `Fin n → ι` is `n * entropy p`, provided
`p` sums to one. This is the i.i.d. special case `r j = p` of the per-coordinate
`Real.entropy_pi_prod`. -/
theorem entropy_pi_prod_of_sum_eq_one {p : ι → ℝ} (hp : ∑ i, p i = 1) (n : ℕ) :
    entropy (fun κ : Fin n → ι ↦ ∏ i, p (κ i)) = n * entropy p := by
  rw [entropy_pi_prod (fun _ ↦ hp), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- **Equality in the entropy bound** (Nielsen–Chuang, *Quantum Computation and Quantum
Information*, Theorem 11.2): for a probability distribution `p` on a nonempty finite type, the
Shannon entropy attains its maximum value `log (card ι)` **if and only if** `p` is the uniform
distribution `i ↦ (card ι)⁻¹`.

Jensen's equality holds iff every `p j` equals the weighted average `∑ i, (card ι)⁻¹ • p i =
(card ι)⁻¹`, and the left-hand side of that Jensen equality rescales to `entropy p = log (card
ι)` after cancelling the common factor `(card ι)⁻¹ > 0`.
-/
theorem entropy_eq_log_card_iff [Nonempty ι] {p : ι → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    entropy p = Real.log (Fintype.card ι) ↔ ∀ i, p i = (Fintype.card ι : ℝ)⁻¹ := sorry

/-- **Sub-normalized cross-entropy bound** (the shared kernel of the support-aware Gibbs
inequalities).

The per-term Gibbs bound `p i * log (q i / p i) ≤ q i - p i` (robust to `q i = 0`, where then `p
i = 0`) sums to `∑ p_i log (q_i / p_i) ≤ ∑ (q i - p i) = ∑ q - ∑ p ≤ 0`; splitting the left side
as `∑ p_i log q_i - ∑ p_i log p_i` gives `entropy p ≤ -∑ p_i log q_i`.
-/
theorem entropy_le_cross_entropy_of_sum_le {p q : ι → ℝ}
    (hp_nn : ∀ i, 0 ≤ p i) (hq_nn : ∀ i, 0 ≤ q i) (hsupp : ∀ i, q i = 0 → p i = 0)
    (hqp_sum : ∑ i, q i ≤ ∑ i, p i) :
    entropy p ≤ -∑ i, p i * Real.log (q i) := by
  -- Per-term Gibbs bound `pᵢ log (qᵢ / pᵢ) ≤ qᵢ - pᵢ`, robust to `qᵢ = 0` since then `pᵢ = 0`.
  have hterm : ∀ i, p i * Real.log (q i / p i) ≤ q i - p i := fun i ↦ by
    rcases eq_or_lt_of_le (hq_nn i) with hq0 | hq0
    · simp [← hq0, hsupp i hq0.symm]
    · exact mul_log_div_le_sub_of_nonneg (hp_nn i) hq0
  have h_sum_le : ∑ i, p i * Real.log (q i / p i) ≤ 0 :=
    calc ∑ i, p i * Real.log (q i / p i)
        ≤ ∑ i, (q i - p i) := Finset.sum_le_sum fun i _ ↦ hterm i
      _ = (∑ i, q i) - ∑ i, p i := by rw [Finset.sum_sub_distrib]
      _ ≤ 0 := by linarith
  -- Split `pᵢ log (qᵢ / pᵢ) = pᵢ log qᵢ - pᵢ log pᵢ`, again handling `qᵢ = 0 ⟹ pᵢ = 0`.
  have h_sum_split : ∑ i, p i * Real.log (q i / p i) =
      ∑ i, p i * Real.log (q i) - ∑ i, p i * Real.log (p i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases eq_or_lt_of_le (hp_nn i) with hp0 | hp0
    · simp [← hp0]
    · rw [Real.log_div (fun hq0 ↦ hp0.ne' (hsupp i hq0)) hp0.ne', mul_sub]
  simp only [entropy_eq, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff]
  linarith [h_sum_le, h_sum_split]

/-- **Gibbs' inequality with support condition** (classical Klein's inequality, general form). -/
theorem entropy_le_cross_entropy_of_support_subset {p q : ι → ℝ}
    (hp_nn : ∀ i, 0 ≤ p i) (hq_nn : ∀ i, 0 ≤ q i) (hsupp : ∀ i, q i = 0 → p i = 0)
    (hpq_sum : ∑ i, p i = ∑ i, q i) :
    entropy p ≤ -∑ i, p i * Real.log (q i) :=
  entropy_le_cross_entropy_of_sum_le hp_nn hq_nn hsupp hpq_sum.ge

/-- **Equality condition for Gibbs' inequality** (Nielsen–Chuang Theorem 11.1).

Together with the `≥ 0` half at the same generality, this is the faithful real-valued rendering
of N&C Theorem 11.1: the relative entropy is non-negative, and vanishes exactly when `p = q`.

**Proof.** The support-aware pointwise Gibbs bound `p x * log (q x / p x) ≤ q x - p x` sums to
`-D(p‖q) ≤ ∑ (q x - p x) = 0`.
-/
theorem relativeEntropy_eq_zero_iff {p q : ι → ℝ} (hp_nn : ∀ i, 0 ≤ p i) (hq_nn : ∀ i, 0 ≤ q i)
    (hsupp : ∀ i, q i = 0 → p i = 0) (hpq_sum : ∑ i, p i = ∑ i, q i) :
    relativeEntropy p q = 0 ↔ p = q := sorry

end Real
