/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy

/-!
# Generalized Klein's inequality

For self-adjoint operators `A, B : E →L[ℂ] E` on a finite-dimensional complex inner product
space and a function `f : ℝ → ℝ` convex on a set `S` containing the spectra of `A` and `B`,
with derivative `f'` at each eigenvalue of `B`, the **generalized Klein inequality**
(Nielsen–Chuang, *Quantum Computation and Quantum Information*, Problem 11.1) states that
`tr(f(A) - f(B)) ≥ tr((A - B) f'(B))`.

## Main results

- `generalized_klein_inequality`: the operator inequality above.
- `ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_nonneg_of_generalizedKlein`:
  **Problem 11.1's deduction** — non-negativity of the quantum relative entropy.
-/

@[expose] public section

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E]

/-- **Generalized Klein's inequality** (Nielsen–Chuang, Problem 11.1).

`re tr((cfc f' B) ∘ (A - B)) ≤ re tr(cfc f A) - re tr(cfc f B)`,

i.e. `tr(f(A) - f(B)) ≥ tr((A - B) f'(B))` in N&C's notation.
-/
theorem generalized_klein_inequality {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {S : Set ℝ} {f f' : ℝ → ℝ} (hf : ConvexOn ℝ S f)
    (hAS : spectrum ℝ A ⊆ S) (hBS : spectrum ℝ B ⊆ S)
    (hderiv : ∀ b ∈ spectrum ℝ B, HasDerivAt f (f' b) b) :
    RCLike.re (LinearMap.trace ℂ E ((cfc f' B).toLinearMap ∘ₗ (A - B).toLinearMap)) ≤
      RCLike.re (LinearMap.trace ℂ E (cfc f A).toLinearMap) -
        RCLike.re (LinearMap.trace ℂ E (cfc f B).toLinearMap) := sorry

namespace ContinuousLinearMap.IsDensityOp

/-- **Non-negativity of the quantum relative entropy** (Nielsen–Chuang, Problem 11.1). For
density operators `ρ, σ` with `σ`'s eigenvalues all positive, `0 ≤ D(ρ ‖ σ)`.
-/
theorem quantumRelativeEntropy_nonneg_of_generalizedKlein {ρ σ : E →L[ℂ] E}
    (hρ : ρ.IsDensityOp) (hσ : σ.IsDensityOp)
    (hσ_pos : ∀ j, 0 < hσ.isSymmetric.eigenvalues rfl j) :
    0 ≤ ρ.quantumRelativeEntropy σ := sorry

end ContinuousLinearMap.IsDensityOp
