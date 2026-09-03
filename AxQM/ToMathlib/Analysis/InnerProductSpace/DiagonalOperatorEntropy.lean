/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropy
public import AxQM.ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl

/-!
# Von Neumann entropy of a diagonal density operator

Fix an orthonormal basis `b` of a finite-dimensional inner product space `E` over `𝕜` and a
*real* weight vector `p : ι → ℝ`. The operator diagonal in `b`,
`b.diagonalOperator (fun i ↦ (p i : 𝕜)) = ∑ᵢ pᵢ • |bᵢ⟩⟨bᵢ|`, is self-adjoint, and this file
relates its operator-level data to the classical distribution `p`.

## Main results

* `OrthonormalBasis.trace_diagonalOperator` — `tr(∑ᵢ wᵢ |bᵢ⟩⟨bᵢ|) = ∑ᵢ wᵢ`.
* `OrthonormalBasis.diagonalOperator_isDensityOp` — a diagonal operator whose real diagonal is a
  probability distribution is a density operator.
-/

@[expose] public section

namespace OrthonormalBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Trace of a diagonal operator**: `tr(∑ᵢ wᵢ |bᵢ⟩⟨bᵢ|) = ∑ᵢ wᵢ`. -/
theorem trace_diagonalOperator (b : OrthonormalBasis ι 𝕜 E) (w : ι → 𝕜) :
    LinearMap.trace 𝕜 E ↑(b.diagonalOperator w) = ∑ i, w i := by
  classical
  rw [LinearMap.trace_eq_sum_inner (↑(b.diagonalOperator w) : E →ₗ[𝕜] E) b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.coe_coe, b.inner_diagonalOperator w i (b i),
    orthonormal_iff_ite.mp b.orthonormal i i, if_pos rfl, mul_one]

/-- A diagonal operator whose (real) diagonal `p` is a **probability distribution** — nonnegative
with `∑ᵢ pᵢ = 1` — is a **density operator**. -/
theorem diagonalOperator_isDensityOp (b : OrthonormalBasis ι 𝕜 E) {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (b.diagonalOperator fun i => (p i : 𝕜)).IsDensityOp := by
  rw [ContinuousLinearMap.isDensityOp_iff]
  refine ⟨b.diagonalOperator_isPositive_of_nonneg _ fun i => RCLike.ofReal_nonneg.mpr (hp i), ?_⟩
  rw [trace_diagonalOperator, ← RCLike.ofReal_sum, hsum, RCLike.ofReal_one]

end OrthonormalBasis
