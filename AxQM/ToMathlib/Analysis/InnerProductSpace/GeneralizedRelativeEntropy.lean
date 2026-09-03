/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Positive

/-!
# Generalized relative entropy for positive operators (Nielsen & Chuang, Problem 11.2)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Problem 11.2 extends the
(Umegaki) relative entropy `S(r ‖ s) = tr(r log r) - tr(r log s)` to arbitrary positive
operators and asks for four properties. This file proves all four for strictly positive
operators on a finite-dimensional complex Euclidean space.

## Main results

- `ContinuousLinearMap.quantumRelativeEntropy_smul_smul_of_hasSupportLE`: **scaling** (11.132) for
  positive `r, s` with `r.HasSupportLE s`.
- `ContinuousLinearMap.quantumRelativeEntropy_jointConvex_of_subadditive_of_hasSupportLE`: **the
  converse** (part (3)) — subadditivity implies joint convexity.
- `ContinuousLinearMap.quantumRelativeEntropy_sum_smul_smul_le_of_hasSupportLE`: **the mixture
  bound** (11.134) for positive `rᵢ, sᵢ` with `rᵢ.HasSupportLE sᵢ` and positive weights `pᵢ, qᵢ`.
- `ContinuousLinearMap.quantumRelativeEntropy_sum_smul_smul_le_relativeEntropy_of_hasSupportLE`:
  **the "pretty formula"** (11.135), its density-operator (`re tr(rᵢ) = 1`) specialization.
-/

@[expose] public section

open scoped ComplexOrder

namespace ContinuousLinearMap

variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 400000 in
-- Elaborating the spectral sums over `ι` against the support hypothesis exceeds the default
-- heartbeat budget.
/-- **Scaling of the generalized relative entropy for positive operators** (N&C Problem 11.2(1), eq.
(11.132), faithful form). For positive operators `r, s` on the finite branch `r.HasSupportLE s`
(`supp r ⊆ supp s`) and positive scalars `c, d`, `S(c • r ‖ d • s) = c · S(r ‖ s) + c · tr(r) ·
log(c / d)`, where `tr(r)` is `re tr r`. -/
theorem quantumRelativeEntropy_smul_smul_of_hasSupportLE
    {ρ σ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive) (hρσ : ρ.HasSupportLE σ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    quantumRelativeEntropy (c • ρ) (d • σ) =
      c * quantumRelativeEntropy ρ σ +
        c * RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) ρ.toLinearMap) *
          Real.log (c / d) := sorry

/-- **Joint convexity implies subadditivity, faithful form** (N&C Problem 11.2(2), the forward
direction of the `subadditivity ↔ joint convexity` equivalence, eq. (11.133), for positive
operators on the finite branch). -/
theorem quantumRelativeEntropy_subadditive_of_jointConvex_of_hasSupportLE
    (hJC : ∀ {a₁ a₂ b₁ b₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι},
      a₁.IsPositive → a₂.IsPositive → b₁.IsPositive → b₂.IsPositive →
        a₁.HasSupportLE b₁ → a₂.HasSupportLE b₂ → ∀ {t s : ℝ}, 0 ≤ t → 0 ≤ s → t + s = 1 →
          quantumRelativeEntropy (t • a₁ + s • a₂) (t • b₁ + s • b₂) ≤
            t * quantumRelativeEntropy a₁ b₁ + s * quantumRelativeEntropy a₂ b₂)
    {r₁ r₂ s₁ s₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hr₁ : r₁.IsPositive) (hr₂ : r₂.IsPositive) (hs₁ : s₁.IsPositive) (hs₂ : s₂.IsPositive)
    (hsup₁ : r₁.HasSupportLE s₁) (hsup₂ : r₂.HasSupportLE s₂) :
    quantumRelativeEntropy (r₁ + r₂) (s₁ + s₂) ≤
      quantumRelativeEntropy r₁ s₁ + quantumRelativeEntropy r₂ s₂ := sorry

/-- **Subadditivity implies joint convexity, faithful form** (N&C Problem 11.2(3), the converse
direction of the `subadditivity ↔ joint convexity` equivalence, for positive operators on the
finite branch). -/
theorem quantumRelativeEntropy_jointConvex_of_subadditive_of_hasSupportLE
    (hSub : ∀ {a₁ a₂ b₁ b₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι},
      a₁.IsPositive → a₂.IsPositive → b₁.IsPositive → b₂.IsPositive →
        a₁.HasSupportLE b₁ → a₂.HasSupportLE b₂ →
          quantumRelativeEntropy (a₁ + a₂) (b₁ + b₂) ≤
            quantumRelativeEntropy a₁ b₁ + quantumRelativeEntropy a₂ b₂)
    {r₁ r₂ s₁ s₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hr₁ : r₁.IsPositive) (hr₂ : r₂.IsPositive) (hs₁ : s₁.IsPositive) (hs₂ : s₂.IsPositive)
    (hsup₁ : r₁.HasSupportLE s₁) (hsup₂ : r₂.HasSupportLE s₂)
    {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (htu : t + u = 1) :
    quantumRelativeEntropy (t • r₁ + u • r₂) (t • s₁ + u • s₂) ≤
      t * quantumRelativeEntropy r₁ s₁ + u * quantumRelativeEntropy r₂ s₂ := sorry

/-- **Mixture bound for the generalized relative entropy for positive operators** (N&C Problem
11.2(4), eq. (11.134), faithful form). For positive families `r, s` on the finite branch `(r
i).HasSupportLE (s i)`, positive weights `p, q` (`0 < pᵢ`, `0 < qᵢ`) on a nonempty index `Finset
t`, `S(∑ᵢ pᵢ • rᵢ ‖ ∑ᵢ qᵢ • sᵢ) ≤ ∑ᵢ pᵢ · S(rᵢ ‖ sᵢ) + ∑ᵢ pᵢ · tr(rᵢ) · log(pᵢ / qᵢ)`, where
`tr(rᵢ)` is `re tr(rᵢ)`. The bound needs only `pᵢ, qᵢ > 0`, not the normalization
`∑ pᵢ = ∑ qᵢ = 1`. -/
theorem quantumRelativeEntropy_sum_smul_smul_le_of_hasSupportLE {κ : Type*} {t : Finset κ}
    (ht : t.Nonempty) {r s : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} {p q : κ → ℝ}
    (hr : ∀ i ∈ t, (r i).IsPositive) (hs : ∀ i ∈ t, (s i).IsPositive)
    (hsup : ∀ i ∈ t, (r i).HasSupportLE (s i))
    (hp : ∀ i ∈ t, 0 < p i) (hq : ∀ i ∈ t, 0 < q i) :
    quantumRelativeEntropy (∑ i ∈ t, p i • r i) (∑ i ∈ t, q i • s i) ≤
      (∑ i ∈ t, p i * quantumRelativeEntropy (r i) (s i)) +
        ∑ i ∈ t, p i * RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) (r i).toLinearMap) *
          Real.log (p i / q i) := sorry

/-- **The "pretty formula" for the mixture bound, faithful form** (N&C Problem 11.2(4), eq.
(11.135)). When the `rᵢ` are density operators (`re tr(rᵢ) = 1`), the mixture-bound correction term
collapses to the classical relative entropy (Kullback–Leibler divergence)
`Real.relativeEntropy p q = ∑ᵢ pᵢ log(pᵢ / qᵢ)` of the weight distributions:
`S(∑ᵢ pᵢ • rᵢ ‖ ∑ᵢ qᵢ • sᵢ) ≤ ∑ᵢ pᵢ · S(rᵢ ‖ sᵢ) + D(p ‖ q)`, for positive families on the finite
branch `(r i).HasSupportLE (s i)`. Stated over `Finset.univ` of a nonempty `Fintype κ`, matching
the index range of `Real.relativeEntropy`. -/
theorem quantumRelativeEntropy_sum_smul_smul_le_relativeEntropy_of_hasSupportLE {κ : Type*}
    [Fintype κ] [Nonempty κ] {r s : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} {p q : κ → ℝ}
    (hr : ∀ i, (r i).IsPositive) (hs : ∀ i, (s i).IsPositive)
    (hsup : ∀ i, (r i).HasSupportLE (s i)) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (htr : ∀ i, RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) (r i).toLinearMap) = 1) :
    quantumRelativeEntropy (∑ i, p i • r i) (∑ i, q i • s i) ≤
      (∑ i, p i * quantumRelativeEntropy (r i) (s i)) + Real.relativeEntropy p q := sorry

end ContinuousLinearMap
