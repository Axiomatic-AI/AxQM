/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingKrausMatrix
import AxQM.Basic.API.BlochState
import AxQM.Basic.API.QuantumChannel
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# AxQM.Basic.API — the amplitude-damping qubit channel

The **single-qubit amplitude-damping channel** `E(ρ) = E₀ ρ E₀† + E₁ ρ E₁†` (Nielsen & Chuang
eq. 10.46, §8.3.5) with operation elements `E₀ = diag(1, √(1-γ))` and `E₁ = √γ |0⟩⟨1|`, packaged as
a genuine `State qubit → State qubit` map.
-/

open Matrix ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The operation elements of the amplitude-damping qubit channel** (Nielsen & Chuang eq. 10.46).
-/
def amplitudeDampingKraus (γ : ℝ) (a : Fin 2) : qubit.space →L[ℂ] qubit.space :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.amplitudeDampingKrausMatrix γ a)

/-- **The completeness relation** `∑ₖ Eₖ† Eₖ = I` for the amplitude-damping operation elements (`0 ≤
γ ≤ 1`), certifying trace preservation. -/
theorem amplitudeDampingKraus_completeness (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    ∑ i, (adjoint (amplitudeDampingKraus γ i)).comp (amplitudeDampingKraus γ i) = 1 := by
  calc ∑ i, (adjoint (amplitudeDampingKraus γ i)).comp (amplitudeDampingKraus γ i)
      = ∑ i, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          ((Concrete.amplitudeDampingKrausMatrix γ i)ᴴ
            * Concrete.amplitudeDampingKrausMatrix γ i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hadj : adjoint (amplitudeDampingKraus γ i)
            = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
                ((Concrete.amplitudeDampingKrausMatrix γ i)ᴴ) :=
          (Matrix.toEuclideanCLM_conjTranspose_eq_adjoint _).symm
        rw [hadj, amplitudeDampingKraus, ← ContinuousLinearMap.mul_def]
        exact (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) _ _).symm
    _ = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          (∑ i, (Concrete.amplitudeDampingKrausMatrix γ i)ᴴ
            * Concrete.amplitudeDampingKrausMatrix γ i) := (map_sum _ _ _).symm
    _ = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) 1 := by
        rw [Concrete.amplitudeDampingKrausMatrix_completeness γ h0 h1]
    _ = 1 := map_one _

/-- **The single-qubit amplitude-damping channel** `E(ρ) = E₀ ρ E₀† + E₁ ρ E₁†` (Nielsen & Chuang
eq. 10.46) as a state map, for damping parameter `0 ≤ γ ≤ 1`: the operator sum of the operation
elements `amplitudeDampingKraus`. -/
def amplitudeDampingChannel (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (ρ : State qubit) : State qubit where
  op := krausSumₗ (amplitudeDampingKraus γ) ρ.op
  isDensity :=
    isDensityOp_krausSumₗ (amplitudeDampingKraus γ) (amplitudeDampingKraus_completeness γ h0 h1)
      ρ.isDensity

end AxQM
