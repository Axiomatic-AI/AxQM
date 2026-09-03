/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumCP
-- `TensorProduct` is re-imported LAST on purpose: it re-asserts the
-- inner-product-space normed structure on `E ⊗[𝕜] F` as the resolution-priority module instance
-- over the bare algebraic one, so operators built with `TensorProduct.map`/`homTensorHomEquiv`
-- unify with the normed module that `rankOne`/`IsPositive` require.

/-!
# The maximally entangled vector of an orthonormal basis

The **Choi–Jamiołkowski** construction (Nielsen–Chuang Theorem 8.1, *Quantum Computation and
Quantum Information*, §8.2.4, Eqs. (8.54)–(8.59)) forms the Choi operator
`σ = (id_R ⊗ Φ)(|α⟩⟨α|)` of a superoperator `Φ` against a maximally entangled reference state
`|α⟩`. This file defines that reference vector.

## Main definitions

* `OrthonormalBasis.maxEntVec b` — the (unnormalized) **maximally entangled vector**
  `|α⟩ = Σᵢ |i⟩ ⊗ |i⟩` for the basis `b`.
-/

open scoped TensorProduct InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

@[expose] public section

namespace OrthonormalBasis

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {ι : Type*} [Fintype ι]

/-- The (unnormalized) **maximally entangled vector** `|α⟩ = Σᵢ |i⟩ ⊗ |i⟩` of an orthonormal basis
`b`, an element of `E ⊗ E`. -/
noncomputable def maxEntVec (b : OrthonormalBasis ι 𝕜 E) : E ⊗[𝕜] E :=
  ∑ i, b i ⊗ₜ[𝕜] b i

end OrthonormalBasis
