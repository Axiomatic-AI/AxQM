/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingChannel
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Concrete: amplitude damping of a general single-qubit density matrix (N&C Exercise 8.22)

The action of the **amplitude-damping channel** `E_AD` (N&C eqs. 8.107–8.108) on a single-qubit
operator `ρ`, in a chosen computational basis `b : OrthonormalBasis (Fin 2) ℂ H`, read off as a
matrix.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- **Exercise 8.22, N&C eq. 8.112 verbatim.** For a genuine single-qubit *state* — matrix
`ρ = !![a, b; b*, c]` with trace `a + c = 1` — amplitude damping gives
`E_AD(ρ) = !![1 - (1-γ)(1-a),  √(1-γ) b;  √(1-γ) b*,  (1-γ) c]`. -/
theorem ampDampChannel_toMatrixOrthonormal_of_trace_one (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (ρ : H →ₗ[ℂ] H)
    (htr : LinearMap.toMatrixOrthonormal b ρ 0 0 + LinearMap.toMatrixOrthonormal b ρ 1 1 = 1) :
    LinearMap.toMatrixOrthonormal b (ampDampChannel b γ ρ)
      = !![1 - ((1 - γ : ℝ) : ℂ) * (1 - LinearMap.toMatrixOrthonormal b ρ 0 0),
            (Real.sqrt (1 - γ) : ℂ) * LinearMap.toMatrixOrthonormal b ρ 0 1;
           (Real.sqrt (1 - γ) : ℂ) * LinearMap.toMatrixOrthonormal b ρ 1 0,
            ((1 - γ : ℝ) : ℂ) * LinearMap.toMatrixOrthonormal b ρ 1 1] := sorry

end AxQM.Concrete

end
