/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.PiTensorProduct
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct
public import Mathlib.LinearAlgebra.Trace

/-!

# Tensor powers of an inner product space

The `n`-fold tensor power of a finite-dimensional inner product space is finite-dimensional.
-/

@[expose] public section

open scoped TensorProduct
open Module

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

namespace PiTensorProduct

/-- The n-fold tensor power of a finite-dimensional space is finite-dimensional. -/
instance instFiniteDimensional_tensorPow (n : ℕ) :
    FiniteDimensional 𝕜 ((⨂[𝕜]^n) E) :=
  Module.Finite.of_basis (Basis.piTensorProduct fun _ : Fin n ↦ Module.finBasis 𝕜 E)

end PiTensorProduct
