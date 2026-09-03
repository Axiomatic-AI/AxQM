/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.Evolution
import AxQM.Concrete.PiEighthGate

/-!
# AxQM.Basic.API — the π/8 (T) gate and `R_z` as qubit evolutions

The physics **underlying operators** for the single-qubit gates of Nielsen & Chuang's Exercise 4.3:
the π/8 gate
`T` and the `z`-axis rotation `R_z(θ)`, each promoted from its concrete `2 × 2` unitary matrix
(`Concrete.tMatrix`, `Concrete.rotZ`) to an `Evolution` of the `qubit`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **π/8 (T) gate** `T` as a closed-system evolution of the `qubit` (Nielsen & Chuang, eq.
4.2). -/
def tGate : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.tMatrix
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) Concrete.tMatrix_mem_unitaryGroup

/-- The **`z`-axis rotation gate** `R_z(θ) = exp(-iθZ/2)` as a closed-system evolution of the
`qubit` (Nielsen & Chuang, eq. 4.6). -/
def rotZGate (θ : ℝ) : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotZ θ)
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) (Concrete.rotZ_mem_unitaryGroup θ)

end AxQM
