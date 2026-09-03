/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import AxQM.ToMathlib.Analysis.InnerProductSpace.MinimalOperatorSum

/-! # The operation-element Gram matrix `Wⱼₖ = tr(Eⱼ† Eₖ)` and the minimal orthogonal family

This file carries out Nielsen & Chuang's **Exercise 8.10** route to Theorem 8.3 (the minimal
operator-sum representation), for a finite family of operation elements `E : ι → (H →L[ℂ] G)`.

## Main definitions

* `ContinuousLinearMap.krausGram` — the operation-element Gram matrix `Wⱼₖ = tr(Eⱼ† Eₖ)`.
* `ContinuousLinearMap.krausDiagonalize` — the Gram-diagonalized family `{Fⱼ}` of operation
  elements, `Fₐ = ∑ᵢ uᵢₐ • Eᵢ`.

## Main results

* `ContinuousLinearMap.krausGram_isHermitian` — `W` is Hermitian, being a Gram matrix.
* `ContinuousLinearMap.krausGram_krausDiagonalize` — the Gram matrix of the diagonalized family is
  diagonal (the eigenvalues of `W`): **the `u W u†` diagonal step**.
* `ContinuousLinearMap.krausSumₗ_krausDiagonalize` — the diagonalized family induces the *same*
  operator-sum map as `E` (unitary freedom, N&C Theorem 8.2).
* `ContinuousLinearMap.krausDiagonalize_card_ne_zero_le_sq` — at most `d²` of the `{Fⱼ}` are
  non-zero.
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace ContinuousLinearMap

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
  {ιb ι : Type*} [Fintype ιb] [Fintype ι]

/-- **The operation-element Gram matrix** of a finite family of operation elements
`E : ι → (H →L[ℂ] G)`, with entries the Hilbert–Schmidt inner products `Wⱼₖ = tr(Eⱼ† Eₖ)` — the
matrix `W` of Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 8.10.

Defined as the Gram matrix (`Matrix.gram`) of the Choi vectors `vec Eⱼ = (matricize b).symm Eⱼ` in
`G ⊗ H`, for an orthonormal basis `b` of the input space `H`. -/
noncomputable def krausGram (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) : Matrix ι ι ℂ :=
  Matrix.gram ℂ (fun j => (TensorProduct.matricize b).symm (E j))

omit [Fintype ι] [FiniteDimensional ℂ H] [FiniteDimensional ℂ G] in
/-- **The operation-element Gram matrix is Hermitian** (N&C Exercise 8.10): `W† = W`, since
`Wₖⱼ = tr(Eₖ† Eⱼ) = conj (tr(Eⱼ† Eₖ)) = conj Wⱼₖ`. A special case of `Matrix.isHermitian_gram`. -/
theorem krausGram_isHermitian (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) :
    (krausGram b E).IsHermitian :=
  Matrix.isHermitian_gram ℂ _

/-- **The rank of the operation-element Gram matrix on a `d`-dimensional system is at most `d²`**
(Nielsen & Chuang, Exercise 8.10). For operation elements `E : ι → (H →L[ℂ] H)` with input and
output space both `H`, `rank W ≤ (dim H)²` — the bound that, after diagonalizing `W`, yields the
`≤ d²` operation elements of Theorem 8.3. -/
theorem krausGram_rank_le_sq (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] H) :
    (krausGram b E).rank ≤ Module.finrank ℂ H ^ 2 := sorry

variable [DecidableEq ι]

/-- **The Gram-diagonalized family of operation elements** `{Fₐ}` of Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 8.10. Diagonalize the Hermitian Gram matrix `W =
krausGram b E` by its eigenvector unitary `u` (`Matrix.IsHermitian.eigenvectorUnitary`, so `u† W
u` is diagonal), and define the recombined operation elements

`Fₐ ≡ ∑ᵢ uᵢₐ • Eᵢ`.
-/
noncomputable def krausDiagonalize (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) :
    ι → H →L[ℂ] G :=
  fun a => ∑ i, ((krausGram_isHermitian b E).eigenvectorUnitary : Matrix ι ι ℂ) i a • E i

omit [FiniteDimensional ℂ H] [FiniteDimensional ℂ G] in
/-- **Diagonalizing `W` orthogonalizes the operation elements** (Nielsen & Chuang, Exercise 8.10).
(`gram (fun a => ∑ᵢ uᵢₐ • vᵢ) = uᴴ * gram v * u`). -/
theorem krausGram_krausDiagonalize (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) :
    krausGram b (krausDiagonalize b E)
      = Matrix.diagonal (RCLike.ofReal ∘ (krausGram_isHermitian b E).eigenvalues) := sorry

omit [FiniteDimensional ℂ H] [FiniteDimensional ℂ G] in
/-- **The diagonalized family induces the same operator-sum map** (Nielsen & Chuang, Exercise 8.10):
`krausSumₗ (krausDiagonalize b E) = krausSumₗ E`, so `{Fⱼ}` is a set of operation elements for
the *same* quantum operation `E`. -/
theorem krausSumₗ_krausDiagonalize [CompleteSpace H] [CompleteSpace G]
    (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) :
    krausSumₗ (krausDiagonalize b E) = krausSumₗ E := sorry

/-- **At most `d²` diagonalized operation elements are non-zero, on a `d`-dimensional system**
(Nielsen & Chuang, Exercise 8.10): the count of non-zero `Fₐ` is `rank W ≤ d²`. -/
theorem krausDiagonalize_card_ne_zero_le_sq (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] H) :
    Nat.card {a // krausDiagonalize b E a ≠ 0} ≤ Module.finrank ℂ H ^ 2 := sorry

end ContinuousLinearMap
