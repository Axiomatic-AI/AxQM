/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Measurement
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM — measuring one factor of a composite system

Given a measurement `m` on a system with outcomes `ι`, the composite system `S ⊗ T` carries the
measurement whose operators act as `m` on one factor and trivially on the other
(`Measurement.onRight`, `Measurement.onLeft`).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {T : QSystem}

namespace Measurement

/-- **Measurement on the right factor** `Nᵢ = 1_S ⊗ Mᵢ` (Nielsen–Chuang §2.2.8). -/
def onRight (m : Measurement ι T) (S : QSystem) : Measurement ι (S ⊗ T) where
  op i := TensorProduct.mapL (1 : S →L[ℂ] S) (m.op i)
  complete := by
    have key : ∀ i, (adjoint (TensorProduct.mapL (1 : S →L[ℂ] S) (m.op i))).comp
        (TensorProduct.mapL (1 : S →L[ℂ] S) (m.op i))
        = TensorProduct.mapL (1 : S →L[ℂ] S) ((adjoint (m.op i)).comp (m.op i)) := by
      intro i
      rw [TensorProduct.mapL_adjoint_comp_self]
      congr 1
      rw [one_def, adjoint_id, id_comp]
    calc ∑ i, (adjoint (TensorProduct.mapL (1 : S →L[ℂ] S) (m.op i))).comp
            (TensorProduct.mapL (1 : S →L[ℂ] S) (m.op i))
        = ∑ i, TensorProduct.mapL (1 : S →L[ℂ] S) ((adjoint (m.op i)).comp (m.op i)) :=
          Finset.sum_congr rfl fun i _ => key i
      _ = TensorProduct.mapL (1 : S →L[ℂ] S) (∑ i, (adjoint (m.op i)).comp (m.op i)) :=
          (TensorProduct.mapL_one_sum_right _).symm
      _ = TensorProduct.mapL (1 : S →L[ℂ] S) 1 := by rw [m.complete]
      _ = 1 := TensorProduct.mapL_one

/-- **Measurement on the left factor** `Nᵢ = Mᵢ ⊗ 1_T` (Nielsen–Chuang §2.2.8). -/
def onLeft {S : QSystem} (m : Measurement ι S) (T : QSystem) : Measurement ι (S ⊗ T) where
  op i := TensorProduct.mapL (m.op i) (1 : T →L[ℂ] T)
  complete := by
    have key : ∀ i, (adjoint (TensorProduct.mapL (m.op i) (1 : T →L[ℂ] T))).comp
        (TensorProduct.mapL (m.op i) (1 : T →L[ℂ] T))
        = TensorProduct.mapL ((adjoint (m.op i)).comp (m.op i)) (1 : T →L[ℂ] T) := by
      intro i
      rw [TensorProduct.mapL_adjoint_comp_self]
      congr 1
      rw [one_def, adjoint_id, id_comp]
    calc ∑ i, (adjoint (TensorProduct.mapL (m.op i) (1 : T →L[ℂ] T))).comp
            (TensorProduct.mapL (m.op i) (1 : T →L[ℂ] T))
        = ∑ i, TensorProduct.mapL ((adjoint (m.op i)).comp (m.op i)) (1 : T →L[ℂ] T) :=
          Finset.sum_congr rfl fun i _ => key i
      _ = TensorProduct.mapL (∑ i, (adjoint (m.op i)).comp (m.op i)) (1 : T →L[ℂ] T) :=
          (TensorProduct.mapL_sum_left _ _).symm
      _ = TensorProduct.mapL (1 : S →L[ℂ] S) (1 : T →L[ℂ] T) := by rw [m.complete]
      _ = 1 := TensorProduct.mapL_one

@[simp]
theorem onLeft_op {S : QSystem} (m : Measurement ι S) (T : QSystem) (i : ι) :
    (m.onLeft T).op i = TensorProduct.mapL (m.op i) (1 : T →L[ℂ] T) := rfl

end Measurement

end AxQM
