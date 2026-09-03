/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationDecomposition
import AxQM.Concrete.RotationConjugation

/-!
# Concrete: the ABC decomposition of a single-qubit unitary (Nielsen & Chuang, Corollary 4.2)

Every single-qubit unitary `U` can be written `U = e^{iα} A X B X C` with `A B C = I`.

## Main declarations
* `exists_abc_decomposition` — **Corollary 4.2 itself**: for `U ∈ Matrix.unitaryGroup (Fin 2) ℂ`
  there exist a real `α` and matrices `A, B, C ∈ Matrix.unitaryGroup (Fin 2) ℂ` with `A B C = 1`
  and `U = e^{iα} • (A X B X C)`, where `X = pauliX`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- `R_y(0) = I`. -/
theorem rotY_zero : rotY 0 = 1 := rotAxis_zero _

/-- **Nielsen & Chuang, Corollary 4.2 (ABC decomposition of a single-qubit unitary).** Every `2 × 2`
unitary `U` (a single-qubit gate, `Uᴴ U = I`) can be written `U = e^{iα} A X B X C` with `A B C
= I`, for a real phase `α`, unitary matrices `A, B, C`, and `X = pauliX`. -/
theorem exists_abc_decomposition (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (α : ℝ) (A B C : Matrix (Fin 2) (Fin 2) ℂ),
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ B ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        C ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ A * B * C = 1 ∧
        U = Complex.exp ((α : ℂ) * Complex.I) • (A * pauliX * B * pauliX * C) := sorry

end AxQM.Concrete
