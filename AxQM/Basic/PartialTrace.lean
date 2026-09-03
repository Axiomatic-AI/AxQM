/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.QSystem
import AxQM.Basic.StateSpace
import AxQM.ToMathlib.Analysis.InnerProductSpace.ReducedState

/-!
# AxQM — reduced states (partial trace)

The **reduced state** (marginal) of a bipartite state of a composite system `S ⊗ T`,
obtained by tracing out one factor (Nielsen–Chuang §2.4.3).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- The **reduced state on the left system**: `ρ_A = Tr_T(ρ_{AB})`, tracing out
the right factor. -/
def State.reducedLeft (ρ : State (S ⊗ T)) : State S where
  op := (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ T.space)
    (ρ.op.toLinearMap : S.space ⊗[ℂ] T.space →ₗ[ℂ] S.space ⊗[ℂ] T.space)).toContinuousLinearMap
  isDensity :=
    ρ.isDensity.of_partialTraceRight_eq (stdOrthonormalBasis ℂ T.space)
      (by rw [LinearMap.coe_toContinuousLinearMap])

/-- The **reduced state on the right system**: `ρ_B = Tr_S(ρ_{AB})`, tracing out
the left factor. -/
def State.reducedRight (ρ : State (S ⊗ T)) : State T where
  op := (LinearMap.partialTraceLeft (stdOrthonormalBasis ℂ S.space)
    (ρ.op.toLinearMap : S.space ⊗[ℂ] T.space →ₗ[ℂ] S.space ⊗[ℂ] T.space)).toContinuousLinearMap
  isDensity :=
    ρ.isDensity.of_partialTraceLeft_eq (stdOrthonormalBasis ℂ S.space)
      (by rw [LinearMap.coe_toContinuousLinearMap])

end AxQM
