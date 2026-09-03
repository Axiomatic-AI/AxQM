/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Convex.FunctionTopology
import Mathlib.Topology.Algebra.Monoid

/-!
# Convexity of a pointwise limit

## Main results

* `ConvexOn.of_tendsto_pointwise_on` and `ConcaveOn.of_tendsto_pointwise_on`: a pointwise-on-`s`
  limit of eventually convex (resp. concave) functions is convex (resp. concave) on `s`.

-/

@[expose] public section

section
open scoped Topology
open Set
variable {𝕜 α β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [PartialOrder β]
    [TopologicalSpace β] [OrderClosedTopology β]
    [AddCommMonoid α] [AddCommMonoid β]
    [SMul 𝕜 α] [SMul 𝕜 β]
    [ContinuousConstSMul 𝕜 β] [ContinuousAdd β]

/-- If a family of functions converges pointwise on `s` to `f`, and the family is eventually
convex on `s`, then `f` is convex on `s`. -/
public theorem ConvexOn.of_tendsto_pointwise_on {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → α → β} {f : α → β} {s : Set α} (hs : Convex 𝕜 s)
    (h_eventually : ∀ᶠ n in l, ConvexOn 𝕜 s (F n))
    (h_tendsto : ∀ x ∈ s, Filter.Tendsto (F · x) l (𝓝 (f x))) :
    ConvexOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy _ _ ha hb hab => le_of_tendsto_of_tendsto
    (h_tendsto _ (hs hx hy ha hb hab))
    (((h_tendsto _ hx).const_smul _).add ((h_tendsto _ hy).const_smul _))
    (h_eventually.mono fun _ hn => hn.2 hx hy ha hb hab)⟩

end

section
open scoped Topology
open Set
variable {𝕜 α β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [PartialOrder β]
    [TopologicalSpace β] [OrderClosedTopology β]
    [AddCommMonoid α] [AddCommMonoid β]
    [SMul 𝕜 α] [SMul 𝕜 β]
    [ContinuousConstSMul 𝕜 β] [ContinuousAdd β]

/-- If a family of functions converges pointwise on `s` to `f`, and the family is eventually
concave on `s`, then `f` is concave on `s`. -/
public theorem ConcaveOn.of_tendsto_pointwise_on {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → α → β} {f : α → β} {s : Set α} (hs : Convex 𝕜 s)
    (h_eventually : ∀ᶠ n in l, ConcaveOn 𝕜 s (F n))
    (h_tendsto : ∀ x ∈ s, Filter.Tendsto (F · x) l (𝓝 (f x))) :
    ConcaveOn 𝕜 s f :=
  ConvexOn.of_tendsto_pointwise_on (β := βᵒᵈ) hs h_eventually h_tendsto

end
