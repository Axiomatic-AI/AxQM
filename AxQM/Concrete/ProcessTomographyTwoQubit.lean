/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ProcessTomography
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Concrete: two-qubit quantum process tomography (Nielsen & Chuang, Exercise 8.34)

Nielsen & Chuang, Exercise 8.34, eqs. (8.180)–(8.181): **two-qubit** quantum process
reconstruction, lifting the single-qubit process-reconstruction identity of Box 8.5.
-/

namespace AxQM.Concrete

open Matrix
open scoped Matrix Kronecker

noncomputable section

/-- Row/column index type of the two-qubit `16 × 16` matrices: `(Fin 2 × Fin 2) × (Fin 2 × Fin 2)`.
The first `Fin 2 × Fin 2` is qubit `1`'s slot, the second qubit `2`'s; each carries the single-qubit
Box 8.5 operator/grid index. -/
abbrev TomoIdx2 : Type := (Fin 2 × Fin 2) × (Fin 2 × Fin 2)

/-- The two-qubit operator basis `Ẽ_M = Ẽ_{m₁} ⊗ Ẽ_{m₂}`, the pairwise Kronecker products of the
single-qubit Box 8.5 basis `{I, X, -iY, Z}` (`tomoBasis`), indexed by `M = (m₁, m₂)`. -/
def tomoBasis2 (M : TomoIdx2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  tomoBasis M.1 ⊗ₖ tomoBasis M.2

/-- Lambda for two qubits: `Λ₂ = Λ ⊗ Λ` (Kronecker square of Box 8.5's `Λ`). -/
def chiLambda2 : Matrix TomoIdx2 TomoIdx2 ℂ :=
  chiLambda ⊗ₖ chiLambda

/-- The two-qubit process `E₂(ρ) = Σ_{MN} χ₂_{MN} Ẽ_M ρ Ẽ_N†`. -/
def chiProcess2 (χ : Matrix TomoIdx2 TomoIdx2 ℂ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ M, ∑ N, χ M N • (tomoBasis2 M * ρ * (tomoBasis2 N)ᴴ)

/-- The block matrix of measured outputs, block `(A, B)` = `E₂(|A⟩⟨B|)`, indexed role-by-role:
the outer index is the two-qubit basis state, the inner index the two-qubit entry. -/
def chiGrid2 (χ : Matrix TomoIdx2 TomoIdx2 ℂ) : Matrix TomoIdx2 TomoIdx2 ℂ :=
  Matrix.of fun U V => chiProcess2 χ (Matrix.single U.1 V.1 1) U.2 V.2

/-- The perfect-shuffle permutation of the four atomic `Fin 2` slots that swaps the middle two
(`(a₁, i₁, a₂, i₂) ↦ (a₁, a₂, i₁, i₂)`), converting the qubit-grouped order to the role-grouped
order. This is Nielsen & Chuang's `I ⊗ SWAP ⊗ I`. -/
def shuffle : Equiv.Perm TomoIdx2 :=
  Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2)

/-- The permutation matrix `P` of the perfect shuffle (`shuffle`); Nielsen & Chuang's
`P = I ⊗ SWAP ⊗ I` from eq. (8.181). -/
def shuffleMatrix : Matrix TomoIdx2 TomoIdx2 ℂ :=
  Equiv.Perm.permMatrix ℂ shuffle

/-- **Two-qubit process reconstruction** (Nielsen & Chuang, Exercise 8.34, eqs. (8.180)–(8.181)):
`χ₂ = Λ₂ (Pᵀ M P) Λ₂`, with `Λ₂ = Λ ⊗ Λ`, `M` the block matrix of measured outputs `E₂(|A⟩⟨B|)`
(`chiGrid2`), and `P` the perfect-shuffle permutation matrix `I ⊗ SWAP ⊗ I`. -/
theorem chiLambda2_chiGrid2_chiLambda2 (χ : Matrix TomoIdx2 TomoIdx2 ℂ) :
    chiLambda2 * (shuffleMatrixᵀ * chiGrid2 χ * shuffleMatrix) * chiLambda2 = χ := sorry

end

end AxQM.Concrete
