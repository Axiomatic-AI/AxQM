/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Hilbert–Schmidt pairing of linear maps

For two linear maps `T, U : E →ₗ[𝕜] F` between finite-dimensional inner product spaces over
`𝕜` (where `𝕜` is `ℝ` or `ℂ`), the **Hilbert–Schmidt pairing** is `trace (U† ∘ T)`.

## Main definitions

- `LinearMap.hsPairing` — the function `(T, U) ↦ trace (U† ∘ T)`.
- `ContinuousLinearMap.hsPairing` — the version for continuous linear maps.
-/

@[expose] public section

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The **Hilbert–Schmidt pairing** of two linear maps: `trace (U† ∘ T)`. -/
noncomputable def hsPairing (T U : E →ₗ[𝕜] F) : 𝕜 :=
  LinearMap.trace 𝕜 E (U.adjoint ∘ₗ T)

theorem hsPairing_eq (T U : E →ₗ[𝕜] F) :
    T.hsPairing U = LinearMap.trace 𝕜 E (U.adjoint ∘ₗ T) := rfl

/-- For a symmetric endomorphism `T`, `re (hsPairing T T) = re (trace (T ∘ₗ T))`. -/
theorem re_hsPairing_self_eq_re_trace_comp_self_of_isSymmetric
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    RCLike.re (T.hsPairing T) = RCLike.re (LinearMap.trace 𝕜 E (T ∘ₗ T)) := by
  rw [hsPairing_eq, hT.adjoint_eq]

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The HS pairing of two continuous linear maps, defined as the HS pairing of their
underlying linear maps. -/
noncomputable def hsPairing (T U : E →L[𝕜] F) : 𝕜 :=
  T.toLinearMap.hsPairing U.toLinearMap

@[simp]
theorem hsPairing_toLinearMap (T U : E →L[𝕜] F) :
    T.toLinearMap.hsPairing U.toLinearMap = T.hsPairing U := rfl

/-- For a self-adjoint operator `T`, `re (hsPairing T T) = re (trace (T * T))`. The
multiplication `T * T : E →L[𝕜] E` coerces to `T.toLinearMap ∘ₗ T.toLinearMap`. -/
theorem re_hsPairing_self_eq_re_trace_sq_of_isSelfAdjoint [CompleteSpace E]
    {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) :
    RCLike.re (T.hsPairing T) =
      RCLike.re (LinearMap.trace 𝕜 E ((T * T : E →L[𝕜] E) : E →ₗ[𝕜] E)) := by
  rw [← hsPairing_toLinearMap]
  exact (LinearMap.re_hsPairing_self_eq_re_trace_comp_self_of_isSymmetric hT.isSymmetric).trans
    rfl

end ContinuousLinearMap
