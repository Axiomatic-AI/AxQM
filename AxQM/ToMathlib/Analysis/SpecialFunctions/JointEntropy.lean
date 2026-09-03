/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Joint entropy, conditional entropy, and mutual information

For finite types `ι`, `κ` and a joint distribution `p : ι × κ → ℝ` (a probability mass function
of a pair of random variables `(X, Y)` when `p ≥ 0` and `∑ p = 1`), this file develops the
elementary information-theoretic quantities built on `Real.entropy`:

## Main results

* `Real.entropy_swap`, `Real.mutualInfo_swap` — **symmetry** (part 1): `H(X, Y) = H(Y, X)` and
  `H(X : Y) = H(Y : X)`.
* `Real.relativeEntropy_indepProd_eq` — (Nielsen–Chuang Exercise 11.5):
  `D(p ‖ p_X ⊗ p_Y) = H(X) + H(Y) - H(X, Y)`.
* `Real.entropy_le_add_marginal` — **subadditivity** (part 4): `H(X, Y) ≤ H(X) + H(Y)`.
* `Real.mutualInfo_nonneg` — `H(X : Y) ≥ 0` (part 5).
* `Real.condEntropy_le_marginalFst` — **conditioning reduces entropy** at the mutual-information
  level: `H(X | Y) ≤ H(X)` (part 5).
* `Real.mutualInfo_eq_zero_iff`, `Real.entropy_add_marginal_eq_iff` — the **equality condition** for
  parts 4/5: subadditivity is saturated iff `X` and `Y` are independent (`p = p_X ⊗ p_Y`).
* `Real.entropy_marginalFst_le` — **the joint entropy dominates the first
  marginal entropy** (part 3): `H(X) ≤ H(X, Y)`.
* `Real.condEntropy_nonneg` — **non-negativity of the conditional entropy** (part 2):
  `H(X | Y) ≥ 0`; `Real.mutualInfo_le_marginalSnd` — `H(X : Y) ≤ H(Y)`.
* `Real.entropy_marginalFst_eq_iff_sndDeterminedByFst`,
  `Real.mutualInfo_eq_marginalSnd_iff_sndDeterminedByFst` — the **equality condition** for parts
  2/3: `H(X) = H(X, Y)` (equivalently `H(X : Y) = H(Y)`) iff `Y` is a deterministic function of `X`
  (`Real.SndDeterminedByFst`).

* `Real.entropy_sub_entropy_marginalFst_eq_relativeEntropy` —
  `H(Y | X) = D(p ‖ Real.condEntropyRef p)`, where `condEntropyRef p (x, y) = p(x, y)² / p_X(x)`.
* `Real.relativeEntropy_condEntropyRef_nonneg` — `H(Y | X) ≥ 0`.
* `Real.relativeEntropy_condEntropyRef_eq_zero_iff` — **the equality condition**: `H(Y | X) = 0` iff
  `Y` is a deterministic function of `X` (`Real.SndDeterminedByFst`).

* `Real.entropy_triple_add_marginal_le` — **strong subadditivity** (part 6; also N&C Exercise 11.6):
  `H(X, Y, Z) + H(Y) ≤ H(X, Y) + H(Y, Z)`.
* `Real.entropy_triple_add_marginal_eq_iff` — the **equality condition** for part 6: strong
  subadditivity is saturated iff `Z → Y → X` forms a Markov chain (`Real.IsMarkovChain`,
  equivalently `X` and `Z` conditionally independent given `Y`).
* `Real.entropy_conditioning_le` — **conditioning reduces entropy** (part 7):
  `H(X | Y, Z) ≤ H(X | Y)`.
-/

@[expose] public section

namespace Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The first marginal `p_X(x) = ∑_y p(x, y)` of a joint distribution `p : ι × κ → ℝ`. -/
noncomputable def marginalFst (p : ι × κ → ℝ) : ι → ℝ := fun x ↦ ∑ y, p (x, y)

/-- The second marginal `p_Y(y) = ∑_x p(x, y)` of a joint distribution `p : ι × κ → ℝ`. -/
noncomputable def marginalSnd (p : ι × κ → ℝ) : κ → ℝ := fun y ↦ ∑ x, p (x, y)

/-- The conditional entropy `H(X | Y) = H(X, Y) - H(Y)` of a joint distribution. -/
noncomputable def condEntropy (p : ι × κ → ℝ) : ℝ := entropy p - entropy (marginalSnd p)

/-- The mutual information `H(X : Y) = H(X) + H(Y) - H(X, Y)` of a joint distribution. -/
noncomputable def mutualInfo (p : ι × κ → ℝ) : ℝ :=
  entropy (marginalFst p) + entropy (marginalSnd p) - entropy p

/-- The product of the marginals `(p_X ⊗ p_Y)(x, y) = p_X(x) · p_Y(y)`: the joint distribution the
pair would have under independence. -/
noncomputable def indepProd (p : ι × κ → ℝ) : ι × κ → ℝ :=
  fun q ↦ marginalFst p q.1 * marginalSnd p q.2

/-- **Symmetry of the joint entropy**: `H(X, Y) = H(Y, X)`. -/
theorem entropy_swap (p : ι × κ → ℝ) : entropy (fun q : κ × ι ↦ p (q.2, q.1)) = entropy p := sorry

/-- **Symmetry of the mutual information**: `H(X : Y) = H(Y : X)`. -/
theorem mutualInfo_swap (p : ι × κ → ℝ) :
    mutualInfo (fun q : κ × ι ↦ p (q.2, q.1)) = mutualInfo p := sorry

/-- **Subadditivity via a relative-entropy identity** (Nielsen & Chuang, Exercise 11.5): the
relative entropy of the joint distribution `p` against the product of its marginals is the
excess of the summed marginal entropies over the joint entropy, `D(p ‖ p_X ⊗ p_Y) = H(X) + H(Y)
- H(X, Y)`. This is the identity N&C Exercise 11.5 asks to establish, `H(p(x, y) ‖ p(x) p(y)) =
H(p(x)) + H(p(y)) - H(p(x, y))`. Valid for any nonnegative `p` (no normalization is needed for
the identity itself). -/
theorem relativeEntropy_indepProd_eq {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    relativeEntropy p (indepProd p)
      = entropy (marginalFst p) + entropy (marginalSnd p) - entropy p := sorry

/-- **Subadditivity of the Shannon entropy** (N&C Theorem 11.3, part 4): the joint entropy of a
probability distribution is at most the sum of its marginal entropies,
`H(X, Y) ≤ H(X) + H(Y)`. -/
theorem entropy_le_add_marginal {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) :
    entropy p ≤ entropy (marginalFst p) + entropy (marginalSnd p) := sorry

/-- **Non-negativity of the mutual information** (N&C Theorem 11.3, part 5): `H(X : Y) ≥ 0`. -/
theorem mutualInfo_nonneg {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) :
    0 ≤ mutualInfo p := sorry

/-- **Conditioning reduces entropy** (N&C Theorem 11.3, part 5): `H(X | Y) ≤ H(X)`. -/
theorem condEntropy_le_marginalFst {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) :
    condEntropy p ≤ entropy (marginalFst p) := sorry

/-- **Equality condition for subadditivity / mutual information** (N&C Theorem 11.3, parts 4 & 5):
`H(X : Y) = 0` iff `X` and `Y` are independent, i.e. `p = p_X ⊗ p_Y`. -/
theorem mutualInfo_eq_zero_iff {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) :
    mutualInfo p = 0 ↔ p = indepProd p := sorry

/-- Subadditivity `H(X, Y) ≤ H(X) + H(Y)` is saturated iff `X` and `Y` are independent. -/
theorem entropy_add_marginal_eq_iff {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) :
    entropy (marginalFst p) + entropy (marginalSnd p) = entropy p ↔ p = indepProd p := sorry

/-- **The joint entropy dominates the first marginal entropy** (N&C Theorem 11.3, part 3): `H(X) ≤
H(X, Y)`. Equivalently the conditional entropy `H(Y | X) = H(X, Y) - H(X)` is nonnegative (part
2). -/
theorem entropy_marginalFst_le {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    entropy (marginalFst p) ≤ entropy p := sorry

/-- **Non-negativity of the conditional entropy** (N&C Theorem 11.3, part 2; N&C Exercise 11.7):
`H(X | Y) = H(X, Y) - H(Y) ≥ 0`. Learning `Y` cannot leave a negative amount of uncertainty about
`X`. -/
theorem condEntropy_nonneg {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) : 0 ≤ condEntropy p := sorry

/-- **`H(X : Y) ≤ H(Y)`** (N&C Theorem 11.3, part 2): the mutual information never exceeds a
marginal entropy. -/
theorem mutualInfo_le_marginalSnd {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    mutualInfo p ≤ entropy (marginalSnd p) := sorry

/-- The second coordinate `Y` is a **deterministic function of the first** `X`. This is the
finite-support rendering of Nielsen & Chuang's "`Y = f(X)`", the equality condition for parts 2
and 3 of Theorem 11.3. -/
def SndDeterminedByFst (p : ι × κ → ℝ) : Prop := ∃ f : ι → κ, ∀ x y, p (x, y) ≠ 0 → y = f x

/-- **Equality condition for `H(X) ≤ H(X, Y)`** (N&C Theorem 11.3, parts 2 & 3): the joint entropy
equals the first marginal entropy iff `Y` is a deterministic function of `X`. -/
theorem entropy_marginalFst_eq_iff_sndDeterminedByFst {p : ι × κ → ℝ} [Nonempty κ]
    (hp : ∀ q, 0 ≤ p q) :
    entropy (marginalFst p) = entropy p ↔ SndDeterminedByFst p := sorry

/-- **Equality condition for `H(X : Y) ≤ H(Y)`** (N&C Theorem 11.3, part 2): the mutual information
equals the second marginal entropy iff `Y` is a deterministic function of `X`. -/
theorem mutualInfo_eq_marginalSnd_iff_sndDeterminedByFst {p : ι × κ → ℝ} [Nonempty κ]
    (hp : ∀ q, 0 ≤ p q) :
    mutualInfo p = entropy (marginalSnd p) ↔ SndDeterminedByFst p := sorry

/-- The **reference distribution** realizing the conditional entropy `H(Y | X)` as a relative
entropy (Nielsen & Chuang, Exercise 11.7): `condEntropyRef p (x, y) = p(x, y)² / p_X(x)`, equal
to `p_X(x) · p(y | x)²` on the support of `p`. -/
noncomputable def condEntropyRef (p : ι × κ → ℝ) : ι × κ → ℝ :=
  fun q ↦ p q ^ 2 / marginalFst p q.1

/-- **Conditional entropy as a relative entropy** (Nielsen & Chuang, Exercise 11.7): this is the
expression the exercise asks for. -/
theorem entropy_sub_entropy_marginalFst_eq_relativeEntropy {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    entropy p - entropy (marginalFst p) = relativeEntropy p (condEntropyRef p) := sorry

/-- **Non-negativity of the conditional entropy, via the relative-entropy expression** (Nielsen &
Chuang, Exercise 11.7). -/
theorem relativeEntropy_condEntropyRef_nonneg {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    0 ≤ relativeEntropy p (condEntropyRef p) := sorry

/-- **Equality condition for the conditional entropy** (Nielsen & Chuang, Exercise 11.7): the
relative-entropy expression `D(p ‖ condEntropyRef p) = H(Y | X)` vanishes if and only if `Y` is a
deterministic function of `X` (`SndDeterminedByFst p`): `H(Y | X) = 0` exactly when conditioning
on `X` removes all uncertainty about `Y`. -/
theorem relativeEntropy_condEntropyRef_eq_zero_iff {p : ι × κ → ℝ} [Nonempty κ]
    (hp : ∀ q, 0 ≤ p q) :
    relativeEntropy p (condEntropyRef p) = 0 ↔ SndDeterminedByFst p := sorry

variable {μ : Type*} [Fintype μ]

/-- The joint `(X, Y)`-marginal `p_{XY}(x, y) = ∑_z p(x, y, z)` of a tripartite distribution,
obtained by summing out the third variable `Z`. -/
noncomputable def marginalFstMid (p : ι × κ × μ → ℝ) : ι × κ → ℝ := fun q ↦ ∑ z, p (q.1, q.2, z)

/-- The middle `Y`-marginal `p_Y(y) = ∑_{x,z} p(x, y, z)` of a tripartite distribution, the first
marginal of the `(Y, Z)`-marginal `marginalSnd p`. -/
noncomputable def marginalMid (p : ι × κ × μ → ℝ) : κ → ℝ := marginalFst (marginalSnd p)

/-- **Strong subadditivity of the Shannon entropy** (N&C Theorem 11.3, part 6; N&C Exercise 11.6):
for a tripartite probability distribution of `(X, Y, Z)`, `H(X, Y, Z) + H(Y) ≤ H(X, Y) + H(Y,
Z)`. -/
theorem entropy_triple_add_marginal_le {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q)
    (hsum : ∑ q, p q = 1) :
    entropy p + entropy (marginalMid p) ≤ entropy (marginalFstMid p) + entropy (marginalSnd p) :=
      sorry

/-- **Conditioning reduces entropy** (N&C Theorem 11.3, part 7): `H(X | Y, Z) ≤ H(X | Y)`. Learning
`Z` in addition to `Y` cannot increase the average uncertainty about `X`. -/
theorem entropy_conditioning_le {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) :
    condEntropy p ≤ condEntropy (marginalFstMid p) := sorry

/-- `Z → Y → X` **forms a Markov chain** — equivalently, `X` and `Z` are conditionally independent
given `Y`. Written division-free as `p(x, y, z) · p_Y(y) = p_{XY}(x, y) · p_{YZ}(y, z)` for all
`x, y, z`. The condition is symmetric in `X` and `Z`, so it equally expresses the chain `X → Y →
Z`. -/
def IsMarkovChain (p : ι × κ × μ → ℝ) : Prop :=
  ∀ x y z, p (x, y, z) * marginalMid p y = marginalFstMid p (x, y) * marginalSnd p (y, z)

/-- **Equality in strong subadditivity** (N&C Theorem 11.3, part 6): strong subadditivity is
saturated iff `Z → Y → X` forms a Markov chain. -/
theorem entropy_triple_add_marginal_eq_iff {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q)
    (hsum : ∑ q, p q = 1) :
    entropy p + entropy (marginalMid p)
        = entropy (marginalFstMid p) + entropy (marginalSnd p) ↔ IsMarkovChain p := sorry

/-- The joint distribution of the reversed triple `(Z, Y, X)`, obtained from the joint distribution
`p` of `(X, Y, Z)` by swapping the outer coordinates: `reverseTriple p (z, y, x) = p (x, y, z)`. -/
def reverseTriple (p : ι × κ × μ → ℝ) : μ × κ × ι → ℝ := fun q ↦ p (q.2.2, q.2.1, q.1)

omit [Fintype κ] in
/-- **N&C Exercise 11.10**: if `X → Y → Z` is a Markov chain, then so is `Z → Y → X`, i.e.
`IsMarkovChain p → IsMarkovChain (reverseTriple p)`. -/
theorem isMarkovChain_reverseTriple {p : ι × κ × μ → ℝ} (h : IsMarkovChain p) :
    IsMarkovChain (reverseTriple p) := sorry

namespace XorMutualInfo

/-- The joint distribution of `(X, Y, Z)` for Nielsen & Chuang Exercise 11.8: `X` and `Y` are
independent uniform bits (values in `ZMod 2`) and `Z = X ⊕ Y` (addition modulo `2`). Each of the
four `(x, y)` combinations has probability `1/4` and forces `z = x + y`; the four inconsistent
triples have probability `0`. -/
noncomputable def xorDist : ZMod 2 × ZMod 2 × ZMod 2 → ℝ :=
  fun q => if q.2.2 = q.1 + q.2.1 then (1 / 4 : ℝ) else 0

/-- The joint distribution of the *pair* `(X, Y)` against `Z`, obtained from `xorDist` by regrouping
the triple as `((X, Y), Z)`. Its mutual information is `H(X, Y : Z)`. -/
noncomputable def xorDistPairZ : (ZMod 2 × ZMod 2) × ZMod 2 → ℝ :=
  fun q => xorDist (q.1.1, q.1.2, q.2)

/-- The joint distribution of `(X, Z)`, the marginal of `xorDist` obtained by summing out `Y`. Its
mutual information is `H(X : Z)`. -/
noncomputable def xorDistXZ : ZMod 2 × ZMod 2 → ℝ := fun q => ∑ y, xorDist (q.1, y, q.2)

/-- The joint distribution of `(Y, Z)`, the marginal of `xorDist` obtained by summing out `X`. Its
mutual information is `H(Y : Z)`. -/
noncomputable def xorDistYZ : ZMod 2 × ZMod 2 → ℝ := fun q => ∑ x, xorDist (x, q.1, q.2)

/-- **Mutual information is not subadditive** (Nielsen & Chuang, Exercise 11.8, eq. (11.34)): for
`X`, `Y` independent uniform bits and `Z = X ⊕ Y`, `H(X, Y : Z) ≰ H(X : Z) + H(Y : Z)`. -/
theorem mutualInfo_xorDist_not_subadditive :
    ¬ mutualInfo xorDistPairZ ≤ mutualInfo xorDistXZ + mutualInfo xorDistYZ := sorry

end XorMutualInfo

end Real
