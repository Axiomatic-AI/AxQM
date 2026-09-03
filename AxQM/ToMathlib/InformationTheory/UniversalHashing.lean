/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.InformationTheory.CollisionEntropy
public import AxQM.ToMathlib.Analysis.SpecialFunctions.MutualInformationMap
public import AxQM.ToMathlib.Analysis.SpecialFunctions.ConditionalEntropyChain

/-!
# Universal hash families and the average collision probability

For a finite family of hash functions `h : γ → α → β` (each `h g : α → β`, with `g` ranging over a
finite index type `γ`) and an input probability distribution `p : α → ℝ`, this file defines
**(2-)universal** hash families and the average collision probability of the hashed output
(Nielsen & Chuang, *Quantum Computation and Quantum Information*, §12.6).
-/

@[expose] public section

namespace Real

variable {α β γ : Type*}

/-- A finite family of hash functions `h : γ → α → β` is **(2-)universal** (Nielsen & Chuang §12.6)
if for every pair of distinct inputs `x ≠ x'`, the fraction of family members `g` that collide
them (`h g x = h g x'`) is at most `1 / |β|`. -/
def IsUniversalFamily [Fintype γ] [Fintype β] [DecidableEq β] (h : γ → α → β) : Prop :=
  ∀ x x' : α, x ≠ x' →
    ((Finset.univ.filter fun g => h g x = h g x').card : ℝ) / Fintype.card γ
      ≤ (Fintype.card β : ℝ)⁻¹

/-- The **average collision probability** of the output `g(X)` of a hash family `h : γ → α → β` on
an input distribution `p : α → ℝ`, averaged over a uniform random member `g`:
`avgCollisionProb h p = (∑_g Real.collisionProb (Real.law p (h g))) / Fintype.card γ`, where
`Real.law p (h g)` is the push-forward distribution of the output `h g`. -/
noncomputable def avgCollisionProb [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    (h : γ → α → β) (p : α → ℝ) : ℝ :=
  (∑ g, collisionProb (law p (h g))) / Fintype.card γ

end Real
