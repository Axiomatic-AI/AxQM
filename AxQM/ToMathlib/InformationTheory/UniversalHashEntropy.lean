/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.UniversalHashing

/-!
# Conditional collision and Shannon entropy of a universal-hash output

The two ordering inequalities of Nielsen & Chuang's privacy-amplification theorem (§12.6,
Theorem 12.16) for the output `G(X)` of a universal hash family `h` applied to an input `X`, with
the hash `G` chosen uniformly at random from the finite family.

## Main results

* `Real.avgCollisionEntropy_ge` — **the corrected (honest) lower bound**, the second inequality of
  Theorem 12.16 with Nielsen & Chuang's constant repaired: for a universal family and any input `p`,
  `Hc(G(X)|G) ≥ log₂|β| - log₂(1 + |β|·Pc(X))`, where `Pc(X) = Real.collisionProb p`. Writing
  `m = log₂|β|` and `2^{m-Hc(X)} = |β|·Pc(X)`, this is `m - log₂(1 + 2^{m-Hc(X)})`. Nielsen & Chuang
  state instead the strictly larger `m - 2^{m-Hc(X)}`, which is **false**.
* `Real.avgCollisionEntropy_le_avgShannonEntropy` — **the first inequality** of the chain,
  `H(G(X)|G) ≥ Hc(G(X)|G)`.
-/

@[expose] public section

namespace Real

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]

/-- The **conditional collision entropy** `Hc(G(X) | G)` of the output of a hash family `h` on an
input distribution `p`, with the hash `G` chosen uniformly: `-log₂` of the average collision
probability (privacy-amplification convention). Note this is `-log₂` of an average, not the average
of the per-`g` collision entropies. -/
noncomputable def avgCollisionEntropy (h : γ → α → β) (p : α → ℝ) : ℝ :=
  -Real.logb 2 (avgCollisionProb h p)

/-- The **conditional Shannon entropy** `H(G(X) | G)` of the output of a hash family `h` on an input
distribution `p`, in bits, with the hash `G` chosen uniformly. -/
noncomputable def avgShannonEntropy (h : γ → α → β) (p : α → ℝ) : ℝ :=
  (∑ g, entropy (law p (h g))) / (Fintype.card γ * Real.log 2)

/-- **The corrected (honest) lower bound on the conditional collision entropy** (Nielsen & Chuang
§12.6, Theorem 12.16, second inequality — with the literal constant repaired). For a
(2-)universal family `h : γ → α → β` and any input probability distribution `p`, `Hc(G(X)|G) ≥
log₂|β| - log₂(1 + |β|·Pc(X))`, where `Pc(X) = collisionProb p`.

Writing `m = log₂|β|` (the number of output bits) and `2^{m-Hc(X)} = |β|·Pc(X)`, the right-hand
side is `m - log₂(1 + 2^{m-Hc(X)})`. This is strictly weaker than Nielsen & Chuang's stated `m -
2^{m-Hc(X)}`, which is **false**.
-/
theorem avgCollisionEntropy_ge [Nonempty β] [Nonempty γ] {h : γ → α → β} (hu : IsUniversalFamily h)
    {p : α → ℝ} (h0 : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    Real.logb 2 (Fintype.card β) - Real.logb 2 (1 + Fintype.card β * collisionProb p)
      ≤ avgCollisionEntropy h p := sorry

/-- **The first inequality** of Nielsen & Chuang Theorem 12.16: `H(G(X)|G) ≥ Hc(G(X)|G)`, the
conditional Shannon entropy of the hashed output dominates its conditional collision entropy. -/
theorem avgCollisionEntropy_le_avgShannonEntropy [Nonempty γ] {h : γ → α → β} {p : α → ℝ}
    (h0 : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    avgCollisionEntropy h p ≤ avgShannonEntropy h p := sorry

end Real
