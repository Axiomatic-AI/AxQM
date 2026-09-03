/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.Density
public import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorPower
public import AxQM.ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Von Neumann entropy of an operator

For a continuous linear operator `T : E →L[𝕜] E` on a finite-dimensional inner product space
over `𝕜` (where `𝕜` is `ℝ` or `ℂ`), the **von Neumann entropy** of `T` is the Shannon entropy
(in nats) of its eigenvalue spectrum.

## Main definitions

- `ContinuousLinearMap.vonNeumannEntropy : (E →L[𝕜] E) → ℝ`
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

open scoped Classical in
/-- The **von Neumann entropy** of an operator: the Shannon entropy of its eigenvalue
spectrum if self-adjoint, with a junk value of `0` otherwise. -/
noncomputable def vonNeumannEntropy (T : E →L[𝕜] E) : ℝ :=
  if h : T.toLinearMap.IsSymmetric
    then Real.entropy fun i : Fin (Module.finrank 𝕜 E) ↦ h.eigenvalues rfl i
    else 0

end ContinuousLinearMap
