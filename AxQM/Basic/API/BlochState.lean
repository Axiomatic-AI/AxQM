/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Qubit
import AxQM.Concrete.BlochMatrix
import AxQM.Concrete.BlochPureState
import AxQM.ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM

/-!
# AxQM.Basic.API — the qubit Bloch state `ρ = ½(I + r·σ)`

The operator-level form promoting the concrete Bloch matrix `Concrete.blochMatrix r = ½(I + r·σ)`
to a genuine density operator of the `qubit`, for a Bloch vector `r` in the closed unit ball
(Nielsen & Chuang, Exercise 2.72(1)(2)).
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

/-- The **Bloch state** `ρ = ½(I + r·σ)` of the qubit, for a Bloch vector `r` in the closed unit
ball `‖r‖² = r₀² + r₁² + r₂² ≤ 1` (Nielsen & Chuang, Exercise 2.72(1), eq. 2.175). -/
def blochState (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) : State qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.blochMatrix r)
  isDensity := by
    rw [ContinuousLinearMap.isDensityOp_iff]
    refine ⟨?_, ?_⟩
    · exact (Matrix.isPositive_toEuclideanCLM_iff _).mpr
        ((Concrete.blochMatrix_posSemidef_iff r).mpr h)
    · exact (Matrix.trace_toEuclideanCLM _).trans (Concrete.blochMatrix_trace r)

/-- The **§1.2 pure state** `|ψ(θ,φ)⟩ = cos(θ/2)|0⟩ + e^{iφ} sin(θ/2)|1⟩` of the qubit (Nielsen &
Chuang eq. 1.4), as a `PureState qubit`: the concrete unit vector `Concrete.blochKet θ φ` embedded
into `EuclideanSpace ℂ (Fin 2)`. It is normalized because `‖cos(θ/2)‖² + ‖e^{iφ} sin(θ/2)‖²
= cos²(θ/2) + sin²(θ/2) = 1` (`‖e^{iφ}‖ = 1`). -/
noncomputable def blochPureState (θ φ : ℝ) : PureState qubit where
  vec := WithLp.toLp 2 (Concrete.blochKet θ φ)
  normalized := by
    change ‖(WithLp.toLp 2 (Concrete.blochKet θ φ) : EuclideanSpace ℂ (Fin 2))‖ = 1
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [Concrete.blochKet, Matrix.cons_val_zero, Matrix.cons_val_one, norm_mul,
      Complex.norm_real, Complex.norm_exp_ofReal_mul_I, one_mul, Real.norm_eq_abs, sq_abs]
    rw [Real.cos_sq_add_sin_sq, Real.sqrt_one]

end AxQM
