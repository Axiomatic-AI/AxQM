/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.HSPairing
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Polar

/-!
# Trace norm of a linear operator on a finite-dimensional inner product space

For a linear map `T : E →ₗ[𝕜] F` between finite-dimensional inner product spaces over `𝕜`
(where `𝕜` is `ℝ` or `ℂ`), the **trace norm** (also known as the nuclear norm or
Schatten 1-norm) is the sum of the singular values of `T`.

## Main definitions

- `LinearMap.traceNorm` — the trace norm as an `ℝ`-valued function.
- `ContinuousLinearMap.traceNorm` — the version for continuous linear maps.
-/

@[expose] public section

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The **trace norm** (Schatten 1-norm) of a linear map between finite-dimensional inner
product spaces: the sum of the singular values of `T`. -/
noncomputable def traceNorm (T : E →ₗ[𝕜] F) : ℝ :=
  ∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i.val

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The trace norm of a continuous linear map, defined as the trace norm of its underlying
linear map. -/
noncomputable def traceNorm (T : E →L[𝕜] F) : ℝ :=
  T.toLinearMap.traceNorm

end ContinuousLinearMap
