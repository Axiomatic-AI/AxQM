/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli
import Mathlib.Data.Matrix.Basis

/-!
# Concrete: single-qubit quantum process tomography

The fixed operator basis and the matrix `Λ` of single-qubit quantum process tomography — Nielsen &
Chuang's Box 8.5, eq. (8.179).
-/

namespace AxQM.Concrete

open Matrix
open scoped Matrix

noncomputable section

/-- Box 8.5 fixed operator basis `{I, X, -iY, Z}`, indexed by `Fin 2 × Fin 2`
(`m ↦ Ẽ_(2·m.1+m.2)`). -/
def tomoBasis : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ
  | (0, 0) => 1
  | (0, 1) => pauliX
  | (1, 0) => (-Complex.I) • pauliY
  | (1, 1) => pauliZ

/-- Lambda from Box 8.5: the block matrix `(1/2)·[[I, X], [X, -I]]`. -/
def chiLambda : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun pq ai =>
    (2 : ℂ)⁻¹ * (if pq.1 = ai.1
                 then (if pq.1 = 0 then 1 else -1) * (if pq.2 = ai.2 then 1 else 0)
                 else (if pq.2 = ai.2 then 0 else 1))

end

end AxQM.Concrete
