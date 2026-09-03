/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Topology.Order.OrderClosed

/-!
# Monotonicity of a pointwise limit

## Main results

* `MonotoneOn.of_tendsto_pointwise_on`, `Monotone.of_tendsto_pointwise` and their antitone
  counterparts: a pointwise limit of eventually monotone (resp. antitone) functions is
  monotone (resp. antitone).

-/

@[expose] public section

section
open Set Filter TopologicalSpace
open OrderDual (toDual)
open scoped Topology
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [TopologicalSpace α] [Preorder α] [t : OrderClosedTopology α]

/-- If a family of functions converges pointwise on `s` to `f`, and the family is eventually
monotone on `s`, then `f` is monotone on `s`. -/
theorem MonotoneOn.of_tendsto_pointwise_on {ι : Type*} {l : Filter ι} [l.NeBot]
    [Preorder β] {s : Set β} {F : ι → β → α} {f : β → α}
    (h_eventually : ∀ᶠ n in l, MonotoneOn (F n) s)
    (h_tendsto : ∀ x ∈ s, Tendsto (F · x) l (𝓝 (f x))) :
    MonotoneOn f s :=
  fun _ hx _ hy hxy ↦ le_of_tendsto_of_tendsto (h_tendsto _ hx) (h_tendsto _ hy)
    (h_eventually.mono fun _ hn ↦ hn hx hy hxy)

end

section
open Set Filter TopologicalSpace
open OrderDual (toDual)
open scoped Topology
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [TopologicalSpace α] [Preorder α] [t : OrderClosedTopology α]

/-- If a family of functions converges pointwise to `f`, and the family is eventually monotone,
then `f` is monotone. -/
theorem Monotone.of_tendsto_pointwise {ι : Type*} {l : Filter ι} [l.NeBot]
    [Preorder β] {F : ι → β → α} {f : β → α}
    (h_eventually : ∀ᶠ n in l, Monotone (F n))
    (h_tendsto : ∀ x, Tendsto (F · x) l (𝓝 (f x))) :
    Monotone f :=
  monotoneOn_univ.mp <| .of_tendsto_pointwise_on
    (h_eventually.mono fun _ hn ↦ hn.monotoneOn _) fun x _ ↦ h_tendsto x

end

section
open Set Filter TopologicalSpace
open OrderDual (toDual)
open scoped Topology
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [TopologicalSpace α] [Preorder α] [t : OrderClosedTopology α]

/-- If a family of functions converges pointwise on `s` to `f`, and the family is eventually
antitone on `s`, then `f` is antitone on `s`. -/
theorem AntitoneOn.of_tendsto_pointwise_on {ι : Type*} {l : Filter ι} [l.NeBot]
    [Preorder β] {s : Set β} {F : ι → β → α} {f : β → α}
    (h_eventually : ∀ᶠ n in l, AntitoneOn (F n) s)
    (h_tendsto : ∀ x ∈ s, Tendsto (F · x) l (𝓝 (f x))) :
    AntitoneOn f s :=
  MonotoneOn.of_tendsto_pointwise_on (α := αᵒᵈ) h_eventually h_tendsto

end

section
open Set Filter TopologicalSpace
open OrderDual (toDual)
open scoped Topology
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [TopologicalSpace α] [Preorder α] [t : OrderClosedTopology α]

/-- If a family of functions converges pointwise to `f`, and the family is eventually antitone,
then `f` is antitone. -/
theorem Antitone.of_tendsto_pointwise {ι : Type*} {l : Filter ι} [l.NeBot]
    [Preorder β] {F : ι → β → α} {f : β → α}
    (h_eventually : ∀ᶠ n in l, Antitone (F n))
    (h_tendsto : ∀ x, Tendsto (F · x) l (𝓝 (f x))) :
    Antitone f :=
  Monotone.of_tendsto_pointwise (α := αᵒᵈ) h_eventually h_tendsto

end
