/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Evolution
import AxQM.Basic.API.BlochState
import AxQM.Basic.API.BlochRotationGate
import AxQM.Concrete.BlochRotation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# AxQM.Basic.API — unitary gates rotate the Bloch sphere (N&C Exercise 8.13)

The operator-level form promoting the concrete `SU(2) → SO(3)` core
(`Concrete.BlochUnitaryRotation`, N&C Exercise 8.13) to the `Evolution`/`State`
layer: a single-qubit unitary gate,
acting on qubit states by conjugation `ρ ↦ U ρ U†` (`Evolution.evolve`), rotates the Bloch vector
by a *proper rotation* `R ∈ SO(3)`. This is the reading of Exercise 8.13 — *unitary
transformations correspond to rotations of the Bloch sphere* — as a statement about state
evolution, not a bare matrix conjugation.

## Main declarations
* `unitaryGate hU` — for a `2 × 2` unitary `U` (`hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ`), the
  **gate** as an `Evolution qubit`, its operator the promotion `Matrix.toEuclideanCLM U` and its
  unitarity transported from `hU` through the `⋆`-algebra isomorphism (exactly the `rotAxisGate`
  pattern, but for an *arbitrary* single-qubit unitary — it ranges over the whole `SU(2)` cover).
* `exists_mem_specialOrthogonalGroup_unitaryGate_evolve_blochState` — **Exercise
  8.13**: for any single-qubit unitary gate there is a proper rotation `R ∈ SO(3)` such that
  its state evolution sends `blochState r` to `blochState (R r)` — unitaries *are* rotations of the
  Bloch sphere.
-/

noncomputable section

namespace AxQM

/-- The **single-qubit unitary gate** of a `2 × 2` unitary `U` (`hU : U ∈ Matrix.unitaryGroup (Fin
2) ℂ`), as a closed-system `Evolution` of the `qubit` (N&C Exercise 8.13). -/
def unitaryGate {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) U
  unitary := Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) hU

/-- **Nielsen & Chuang, Exercise 8.13 — unitary transformations correspond to
rotations of the Bloch sphere.** For any single-qubit unitary `U`, the state evolution `ρ ↦ U ρ
U†` (`unitaryGate hU |>.evolve`) acts on the Bloch state `blochState r = ½(I + r·σ)` as a
*proper rotation* of its Bloch vector: there is `R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ`
with `(unitaryGate hU).evolve (blochState r) = blochState (R r)` for every Bloch vector `r`.
-/
theorem exists_mem_specialOrthogonalGroup_unitaryGate_evolve_blochState
    {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1)
        (h' : (R.mulVec r) 0 ^ 2 + (R.mulVec r) 1 ^ 2 + (R.mulVec r) 2 ^ 2 ≤ 1),
        (unitaryGate hU).evolve (blochState r h) = blochState (R.mulVec r) h' := sorry

end AxQM
