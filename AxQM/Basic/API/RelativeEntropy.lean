/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Entropy
import AxQM.Basic.PartialTrace
import AxQM.ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
import AxQM.ToMathlib.Analysis.InnerProductSpace.ReducedState
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedKleinInequality
import AxQM.ToMathlib.Analysis.InnerProductSpace.Positive

/-!
# AxQM — quantum relative entropy of two states

The **quantum relative entropy** (Umegaki relative entropy) of a state `ρ` with respect to a state
`σ` (Nielsen–Chuang §11.3.1, eq. (11.55)) is `S(ρ ‖ σ) = tr(ρ log ρ) − tr(ρ log σ)`.

## Main definitions

* `AxQM.State.quantumRelativeEntropy` — the relative entropy `S(ρ ‖ σ)` of states `ρ, σ`.

## Main results

* `AxQM.State.quantumRelativeEntropy_nonneg_of_hasSupportLE` — **Klein's inequality** (N&C
  Theorem 11.7), the faithful finite-branch form: `S(ρ ‖ σ) ≥ 0` whenever `supp ρ ⊆ supp σ`
  (`ρ.op.HasSupportLE σ.op`), no faithfulness of `σ`.
* `AxQM.State.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE` — **Klein's inequality,
  equality condition** (N&C Theorem 11.7): for `supp ρ ⊆ supp σ`, `S(ρ ‖ σ) = 0 ↔ ρ = σ`.
* `AxQM.State.quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE` — **joint
  convexity of the relative entropy** (N&C Theorem 11.12), the faithful finite-branch form: the
  `n`-ary `S(∑ wₖ ρₖ ‖ ∑ wₖ σₖ) ≤ ∑ wₖ S(ρₖ‖σₖ)` under only the **support condition**
  `(ρₖ).op.HasSupportLE (σₖ).op` on each component — no faithfulness (rank-deficient states
  allowed).
* `AxQM.State.quantumRelativeEntropy_jointly_convex_of_hasSupportLE` — its **two-point
  form** `S(t ρ₁+s ρ₂ ‖ t σ₁+s σ₂) ≤ t S(ρ₁‖σ₁)+s S(ρ₂‖σ₂)`, N&C's literal statement.
* `AxQM.State.quantumRelativeEntropy_reduced_le_of_hasSupportLE` — **monotonicity under the
  partial trace** (N&C Theorem 11.17), the **faithful finite-branch form**: tracing out the right
  subsystem cannot increase the relative entropy, `S(ρ_A ‖ σ_A) ≤ S(ρ_AB ‖ σ_AB)`, under only the
  **support condition** `ρ.op.HasSupportLE σ.op` — no faithfulness (rank-deficient states allowed);
  the bridge to strong subadditivity.
-/

namespace AxQM

variable {S : QSystem}

/-- The **quantum relative entropy** `S(ρ ‖ σ) = tr(ρ log ρ) − tr(ρ log σ)` of a state `ρ` with
respect to a state `σ` (Nielsen–Chuang §11.3.1, eq. (11.55)). -/
noncomputable def State.quantumRelativeEntropy (ρ σ : State S) : ℝ :=
  ρ.op.quantumRelativeEntropy σ.op

/-- **Klein's inequality** (Nielsen–Chuang Theorem 11.7), on the finite branch. The quantum relative
entropy of two states is non-negative, `S(ρ ‖ σ) ≥ 0`, whenever the **support condition** `supp
ρ ⊆ supp σ` holds — `ρ.op.HasSupportLE σ.op`, i.e. `ker σ.op ≤ ker ρ.op` — with **no
faithfulness of `σ` required**.

This is N&C's theorem stated on exactly the branch where the relative entropy is finite: N&C
define `S(ρ ‖ σ) = +∞` when `supp ρ ⊄ supp σ` and finite otherwise, and the support condition
`ρ.op.HasSupportLE σ.op` is precisely that "finite otherwise" clause — the natural domain of the
real-valued quantity, not an added hypothesis narrowing the claim.
-/
theorem State.quantumRelativeEntropy_nonneg_of_hasSupportLE (ρ σ : State S)
    (h : ρ.op.HasSupportLE σ.op) : 0 ≤ ρ.quantumRelativeEntropy σ := sorry

/-- **Klein's inequality, equality condition** (Nielsen–Chuang Theorem 11.7), on the finite branch.
For states satisfying the **support condition** `supp ρ ⊆ supp σ` (`ρ.op.HasSupportLE σ.op`,
i.e. `ker σ.op ≤ ker ρ.op`), the quantum relative entropy vanishes iff the states coincide, `S(ρ
‖ σ) = 0 ↔ ρ = σ` — with **no faithfulness of `σ` required**.
-/
theorem State.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE (ρ σ : State S)
    (h : ρ.op.HasSupportLE σ.op) : ρ.quantumRelativeEntropy σ = 0 ↔ ρ = σ := sorry

/-- **Joint convexity of the quantum relative entropy, `n`-ary form** (Nielsen–Chuang Theorem
11.12), the **faithful finite-branch statement**.

This is N&C's theorem stated on exactly the branch where the relative entropy is finite — N&C's
`S(ρ ‖ σ) = +∞` when `supp ρ ⊄ supp σ`, finite otherwise — with **no faithfulness (strict
positivity) required**; rank-deficient constituents are allowed. The support condition is
precisely that "finite otherwise" clause, the natural domain of the real-valued quantity (`cfc
Real.log` sends the zero eigenvalues of a rank-deficient operator to `0` rather than `−∞`), not
a hypothesis narrowing the claim.
-/
theorem State.quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE
    {κ : Type*} (u : Finset κ) (ρ σ : State S) (ρs σs : κ → State S) (w : κ → ℝ)
    (hsupp : ∀ k ∈ u, (ρs k).op.HasSupportLE (σs k).op)
    (hw₀ : ∀ k ∈ u, 0 ≤ w k) (hw₁ : ∑ k ∈ u, w k = 1)
    (hρ : ρ.op = ∑ k ∈ u, w k • (ρs k).op)
    (hσ : σ.op = ∑ k ∈ u, w k • (σs k).op) :
    ρ.quantumRelativeEntropy σ ≤ ∑ k ∈ u, w k * (ρs k).quantumRelativeEntropy (σs k) := sorry

/-- **Joint convexity of the quantum relative entropy, two-point form** (Nielsen–Chuang Theorem
11.12), the **faithful finite-branch statement** and N&C's literal two-point claim: for states
with the **support conditions** `ρ₁.op.HasSupportLE σ₁.op` and `ρ₂.op.HasSupportLE σ₂.op` and
probabilities `t, s ≥ 0`, `t + s = 1`, if `ρ = t ρ₁ + s ρ₂` and `σ = t σ₁ + s σ₂` (as density
operators), then `S(ρ ‖ σ) ≤ t · S(ρ₁ ‖ σ₁) + s · S(ρ₂ ‖ σ₂)`.

**No strict positivity is required** — only the support condition, N&C's "finite otherwise"
branch.
-/
theorem State.quantumRelativeEntropy_jointly_convex_of_hasSupportLE
    (ρ σ ρ₁ ρ₂ σ₁ σ₂ : State S)
    (hs₁ : ρ₁.op.HasSupportLE σ₁.op) (hs₂ : ρ₂.op.HasSupportLE σ₂.op)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1)
    (hρ : ρ.op = t • ρ₁.op + s • ρ₂.op)
    (hσ : σ.op = t • σ₁.op + s • σ₂.op) :
    ρ.quantumRelativeEntropy σ ≤
      t * ρ₁.quantumRelativeEntropy σ₁ + s * ρ₂.quantumRelativeEntropy σ₂ := sorry

/-- **Monotonicity of the quantum relative entropy under the partial trace, on the support
condition** (Nielsen–Chuang Theorem 11.17), the **faithful finite-branch statement**. Tracing out
the right subsystem cannot increase the relative entropy,

`S(ρ_A ‖ σ_A) ≤ S(ρ_AB ‖ σ_AB)`,

where `ρ_A = Tr_T ρ = ρ.reducedLeft` (and likewise for `σ`), whenever the **support condition**
`supp ρ ⊆ supp σ` holds — `ρ.op.HasSupportLE σ.op` (`ker σ.op ≤ ker ρ.op`) — with **no faithfulness
(strict positivity) of either state required**.

This is N&C's theorem stated on exactly the branch where the relative entropy is finite: N&C define
`S(ρ ‖ σ) = +∞` when `supp ρ ⊄ supp σ` and finite otherwise, and the support condition
`ρ.op.HasSupportLE σ.op` is precisely that "finite otherwise" clause — the natural domain of the
real-valued quantity (`cfc Real.log` sends the zero eigenvalues of a rank-deficient operator to `0`
rather than `−∞`), not a hypothesis narrowing the claim. Rank-deficient `ρ, σ` are admitted; the
marginal support condition `supp ρ_A ⊆ supp σ_A` needed for the left-hand side descends from the
joint one automatically inside the fork proof.
-/
theorem State.quantumRelativeEntropy_reduced_le_of_hasSupportLE {S T : QSystem}
    (ρ σ : State (S.compose T)) (hsupp : ρ.op.HasSupportLE σ.op) :
    ρ.reducedLeft.quantumRelativeEntropy σ.reducedLeft ≤ ρ.quantumRelativeEntropy σ := sorry

end AxQM
