/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
public import AxQM.ToMathlib.Analysis.RCLike.Basic

/-!
# Pushforward (coarse-graining) of a POVM along a function on outcomes

Given a POVM `M : POVM ι 𝕜 E` and a function `g : ι → κ` on the outcome index, the **pushforward**
`M.map g : POVM κ 𝕜 E` is the POVM whose effect at `k` groups (sums) the effects of all original
outcomes lying over `k`.

## Main definitions / results

* `POVM.map` — the pushforward POVM along `g : ι → κ`.
* `POVM.map_elements` — its effects, `(M.map g).elements k = ∑_{g i = k} M.elements i`.
* `POVM.map_toPMF` — its Born rule, `(M.map g).toPMF ρ k = ∑_{g i = k} M.toPMF ρ i`.
-/

@[expose] public section

open scoped BigOperators

namespace POVM

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Pushforward of a POVM along a function on outcomes.** For a POVM `M : POVM ι 𝕜 E` and a
function `g : ι → κ`, `M.map g` is the POVM on the outcome set `κ` whose effect at `k` is the
sum of the effects of the original outcomes in the fibre `g⁻¹{k}`: `(M.map g).elements k = ∑_{i
: g i = k} M.elements i`. Injective `g` gives a relabelling; general `g` a coarse-graining that
merges outcomes. -/
noncomputable def map (M : POVM ι 𝕜 E) (g : ι → κ) : POVM κ 𝕜 E where
  elements k := ∑ i ∈ Finset.univ.filter (fun i => g i = k), M.elements i
  isPositive k := ContinuousLinearMap.isPositive_sum _ fun i _ => M.isPositive i
  sum_eq_one := by
    rw [Finset.sum_fiberwise Finset.univ g M.elements]; exact M.sum_eq_one

@[simp]
theorem map_elements (M : POVM ι 𝕜 E) (g : ι → κ) (k : κ) :
    (M.map g).elements k = ∑ i ∈ Finset.univ.filter (fun i => g i = k), M.elements i := rfl

/-- **Born rule of the pushforward POVM.** The probability the coarse-grained POVM `M.map g` assigns
to the merged outcome `k` on a state `ρ` is the sum of the probabilities `M` assigns to the original
outcomes lying over `k`: `(M.map g).toPMF ρ k = ∑_{i : g i = k} M.toPMF ρ i`. -/
theorem map_toPMF [FiniteDimensional 𝕜 E] (M : POVM ι 𝕜 E) (g : ι → κ) (ρ : E →L[𝕜] E) (k : κ) :
    (M.map g).toPMF ρ k = ∑ i ∈ Finset.univ.filter (fun i => g i = k), M.toPMF ρ i := by
  simp only [toPMF_eq, map_elements]
  rw [← RCLike.re_sum, ← map_sum (LinearMap.trace 𝕜 E), ← ContinuousLinearMap.coe_sum,
    ← ContinuousLinearMap.finset_sum_comp]

end POVM
