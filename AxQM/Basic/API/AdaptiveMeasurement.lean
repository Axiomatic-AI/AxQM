/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CascadedMeasurement
import AxQM.Basic.API.CompositeMeasurement
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# AxQM — the adaptive cascade of measurements (dependent Exercise 2.57)

The **adaptive cascade** generator `L.adaptiveCascade M`: given a measurement `L` with outcomes `κ`
and, for *each* outcome `j : κ`, a measurement `M j` with outcomes `μ j` (the second measurement is
allowed to *depend on the first outcome*), the composite that measures `L` and then the
outcome-dependent `M j` is itself a single measurement, with outcome set the sigma type
`Σ j, μ j`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {κ : Type*} [Fintype κ] {μ : κ → Type*} [∀ j, Fintype (μ j)] {S : QSystem}

namespace Measurement

/-- The **adaptive cascade** of a measurement `L` (outcomes `κ`) with an outcome-dependent family of
measurements `M j` (outcomes `μ j`): the single measurement with outcome set `Σ j, μ j` whose
operator for outcome `⟨j, k⟩` is `N₍ⱼ,ₖ₎ = (M j)ₖ Lⱼ`. The second measurement is chosen
conditionally on the first outcome `j`. -/
def adaptiveCascade (L : Measurement κ S) (M : (j : κ) → Measurement (μ j) S) :
    Measurement (Σ j, μ j) S where
  op p := ((M p.1).op p.2).comp (L.op p.1)
  complete := by
    rw [← L.complete, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsummand : ∀ k : μ j,
        (adjoint (((M j).op k).comp (L.op j))).comp (((M j).op k).comp (L.op j))
          = (adjoint (L.op j)).comp
              (((adjoint ((M j).op k)).comp ((M j).op k)).comp (L.op j)) :=
      fun k => by rw [adjoint_comp, comp_assoc, comp_assoc]
    simp only [hsummand]
    rw [← ContinuousLinearMap.comp_finset_sum, ← ContinuousLinearMap.finset_sum_comp,
      (M j).complete, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

end Measurement

end AxQM
