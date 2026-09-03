/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.Polar

/-!

# Unitary polar decomposition of a square operator

For a continuous linear operator `A : E →L[𝕜] E` on a finite-dimensional inner product space,
this file gives the classical **unitary** polar decomposition.

## Main results

* `ContinuousLinearMap.exists_unitary_isPositive_polar`: the full two-sided decomposition
  `A = U J = K U` with `U` unitary and `J`, `K` positive satisfying `J² = A† A`,
  `K² = A A†`.
* `ContinuousLinearMap.absoluteValue_eq_of_unitary_comp` /
  `ContinuousLinearMap.adjoint_absoluteValue_eq_of_comp_unitary`: **uniqueness of `J`, `K`** —
  any positive operator appearing as the right (resp. left) factor of a unitary factorisation
  of `A` equals `|A|` (resp. `|A†|`).
* `ContinuousLinearMap.unitary_factor_unique_of_isUnit`: **uniqueness of `U`** when `A` is
  invertible.
-/

@[expose] public section

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]

open Module InnerProductSpace
open scoped InnerProduct

namespace ContinuousLinearMap

variable (A : E →L[𝕜] E)

/-- **Polar decomposition — existence** (Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Theorem 2.3). For a square operator `A : E →L[𝕜] E` there exist a unitary `U` and
positive operators `J`, `K` with

`A = U ∘L J = K ∘L U`,  `J ∘L J = A† ∘L A`,  `K ∘L K = A ∘L A†`.
-/
theorem exists_unitary_isPositive_polar :
    ∃ U ∈ unitary (E →L[𝕜] E), ∃ J K : E →L[𝕜] E,
      J.IsPositive ∧ K.IsPositive ∧ A = U ∘L J ∧ A = K ∘L U ∧
        J ∘L J = A.adjoint ∘L A ∧ K ∘L K = A ∘L A.adjoint := sorry

/-- **Uniqueness of the positive right factor `J`.** If `A = U' ∘L J'` with `U'` unitary and
`J'` positive, then `J' = |A| = √(A† A)`. -/
theorem absoluteValue_eq_of_unitary_comp {U' J' : E →L[𝕜] E}
    (hU' : U' ∈ unitary (E →L[𝕜] E)) (hJ' : J'.IsPositive) (h : A = U' ∘L J') :
    J' = A.absoluteValue := sorry

/-- **Uniqueness of the positive left factor `K`.** If `A = K' ∘L U'` with `U'` unitary and `K'`
positive, then `K' = |A†| = √(A A†)`. -/
theorem adjoint_absoluteValue_eq_of_comp_unitary {U' K' : E →L[𝕜] E}
    (hU' : U' ∈ unitary (E →L[𝕜] E)) (hK' : K'.IsPositive) (h : A = K' ∘L U') :
    K' = A.adjoint.absoluteValue := sorry

/-- **Uniqueness of the unitary factor `U` for invertible `A`.** If `A` is invertible and `A = U₁ ∘L
J₁ = U₂ ∘L J₂` are two unitary–positive factorisations, then `U₁ = U₂`. -/
theorem unitary_factor_unique_of_isUnit {U₁ U₂ J₁ J₂ : E →L[𝕜] E} (hA : IsUnit A)
    (hU₁ : U₁ ∈ unitary (E →L[𝕜] E)) (hU₂ : U₂ ∈ unitary (E →L[𝕜] E))
    (hJ₁ : J₁.IsPositive) (hJ₂ : J₂.IsPositive)
    (h₁ : A = U₁ ∘L J₁) (h₂ : A = U₂ ∘L J₂) : U₁ = U₂ := sorry

end ContinuousLinearMap
