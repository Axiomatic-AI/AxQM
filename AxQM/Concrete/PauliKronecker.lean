/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import AxQM.Concrete.PauliOuterProduct

/-!
# Concrete: Kronecker products of the Pauli matrices (Nielsen & Chuang, Exercise 2.27)

This file computes the explicit `4 × 4` matrix representations of a few tensor products of Pauli
matrices and shows that the tensor (Kronecker) product is not commutative.

## Contents

* `flattenFin4` — the `Fin 2 × Fin 2 → Fin 4` re-indexing of a two-factor tensor
  product to its flat `4 × 4` matrix.
* `flattenFin4_pauliX_kronecker_pauliZ`, `flattenFin4_pauliI_kronecker_pauliX`,
  `flattenFin4_pauliX_kronecker_pauliI` — parts (a), (b), (c): the explicit `4 × 4`
  matrices.
* `pauliI_kronecker_pauliX_ne_pauliX_kronecker_pauliI` — the tensor product is **not**
  commutative: `I ⊗ X ≠ X ⊗ I`. This is the final question of the exercise.
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

/-- Flatten a `Fin 2 × Fin 2`-indexed matrix (a two-factor tensor product) to its `4 × 4`
matrix representation, ordering the product index by
`finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4`, `(i, j) ↦ 2 * i + j` — i.e. the
computational-basis order `|00⟩, |01⟩, |10⟩, |11⟩`. -/
def flattenFin4 (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv M

/-- Matrix representation of `X ⊗ Z` (Nielsen & Chuang, Exercise 2.27(a)). -/
theorem flattenFin4_pauliX_kronecker_pauliZ :
    flattenFin4 (pauliX ⊗ₖ pauliZ) =
      !![0, 0, 1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, -1, 0, 0] := sorry

/-- Matrix representation of `I ⊗ X` (Nielsen & Chuang, Exercise 2.27(b)). -/
theorem flattenFin4_pauliI_kronecker_pauliX :
    flattenFin4 (pauliI ⊗ₖ pauliX) =
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := sorry

/-- Matrix representation of `X ⊗ I` (Nielsen & Chuang, Exercise 2.27(c)). -/
theorem flattenFin4_pauliX_kronecker_pauliI :
    flattenFin4 (pauliX ⊗ₖ pauliI) =
      !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0] := sorry

/-- The tensor (Kronecker) product is **not** commutative: `I ⊗ X ≠ X ⊗ I`. This answers the
final question of Nielsen & Chuang, Exercise 2.27. -/
theorem pauliI_kronecker_pauliX_ne_pauliX_kronecker_pauliI :
    pauliI ⊗ₖ pauliX ≠ pauliX ⊗ₖ pauliI := sorry

end AxQM.Concrete
