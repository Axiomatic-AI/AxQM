/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenvalues of a unitary operator have modulus one

Let `H` be a complex (or, more generally, `RCLike`) Hilbert space. This file records that every
eigenvalue of a unitary operator on `H` has modulus one — Nielsen & Chuang, Exercise 2.18.

## Main results

* `Module.End.HasEigenvalue.norm_eq_one_of_mem_unitary`: any eigenvalue of a unitary operator
  `U ∈ unitary (H →L[𝕜] H)` on a Hilbert space has modulus one.
-/

@[expose] public section

namespace Module.End

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Nielsen & Chuang, Exercise 2.18.** Every eigenvalue of a unitary operator on a Hilbert space
has modulus one: if `U ∈ unitary (H →L[𝕜] H)` and `μ` is an eigenvalue of `U`, then `‖μ‖ = 1`.
-/
theorem HasEigenvalue.norm_eq_one_of_mem_unitary {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] {U : H →L[𝕜] H} {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (U : H →ₗ[𝕜] H) μ) (hU : U ∈ unitary (H →L[𝕜] H)) : ‖μ‖ = 1 :=
      sorry

end Module.End
