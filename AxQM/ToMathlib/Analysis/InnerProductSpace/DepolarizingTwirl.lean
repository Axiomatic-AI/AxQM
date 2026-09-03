/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl

/-!
# The depolarizing twirl: a finite unitary `1`-design

A finite unitary `1`-design on a finite-dimensional inner product space `E` of dimension `d` is a
finite family of unitaries `Uⱼ` with weights `pⱼ` for which the averaged conjugation
`A ↦ ∑ⱼ pⱼ Uⱼ A Uⱼ†` is the **completely depolarizing channel** `A ↦ (tr A / d) • I`.

## Main definitions

* `OrthonormalBasis.signDiagonalEquiv` — the sign-diagonal unitary `Sε` (`ε : ι → Bool`) of an
  orthonormal basis, as a `LinearIsometryEquiv`.
* `OrthonormalBasis.depolarizingUnitary` — the composites `Pσ ∘ Sε` of a sign-diagonal unitary and
  a basis-permutation unitary `Pσ` (`σ : Equiv.Perm ι`).

## Main results

* `LinearIsometryEquiv.exists_conjStarAlgEquiv_oneDesign` — Nielsen & Chuang, Exercise 11.19: a
  finite unitary `1`-design exists on every nontrivial finite-dimensional space.
-/

@[expose] public section

open Module InnerProductSpace ContinuousLinearMap

namespace OrthonormalBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (b : OrthonormalBasis ι 𝕜 E)

section CompleteSpace

variable [CompleteSpace E]

/-- The **sign-diagonal unitary** `Sε = ∑ᵢ (-1)^{ε i} |bᵢ⟩⟨bᵢ|` packaged as a
`LinearIsometryEquiv`. -/
noncomputable def signDiagonalEquiv (ε : ι → Bool) : E ≃ₗᵢ[𝕜] E :=
  Unitary.linearIsometryEquiv ⟨b.signDiagonal ε, b.signDiagonal_mem_unitary ε⟩

variable [DecidableEq ι]

/-- The **depolarizing unitaries**: the composites `Pσ ∘ Sε` of a sign-diagonal unitary `Sε` and a
basis permutation `Pσ`, indexed by `(ε, σ) : (ι → Bool) × Equiv.Perm ι`. -/
noncomputable def depolarizingUnitary (p : (ι → Bool) × Equiv.Perm ι) : E ≃ₗᵢ[𝕜] E :=
  (b.signDiagonalEquiv p.1).trans (b.equiv b p.2)

end CompleteSpace

end OrthonormalBasis

namespace LinearIsometryEquiv

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- **There is a finite unitary `1`-design realising the completely depolarizing channel**
(Nielsen & Chuang, Exercise 11.19, existential form). On any nontrivial finite-dimensional inner
product space of dimension `d = finrank 𝕜 E`, there exist a finite family of unitaries
`Uⱼ : E ≃ₗᵢ[𝕜] E` and a probability distribution `pⱼ` such that for **every** operator `A`,

`∑ⱼ pⱼ Uⱼ A Uⱼ† = (tr A / d) • I`.
-/
theorem exists_conjStarAlgEquiv_oneDesign [Nontrivial E] :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → (E ≃ₗᵢ[𝕜] E)) (p : ι → ℝ),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
        ∀ A : E →L[𝕜] E, ∑ i, (p i : 𝕜) • (U i).conjStarAlgEquiv A
          = (LinearMap.trace 𝕜 E (A : E →ₗ[𝕜] E) / (Module.finrank 𝕜 E : 𝕜)) • (1 : E →L[𝕜] E) :=
            sorry

end LinearIsometryEquiv
