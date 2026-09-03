/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace
import AxQM.ToMathlib.Analysis.InnerProductSpace.PostMeasurement
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
import AxQM.ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# AxQM — measurement, the Born rule, and collapse

The primitive for a **measurement** on a system `S`: a finite family of
*measurement operators* `Mᵢ` with the completeness relation `∑ᵢ Mᵢ† Mᵢ = 1`
(N&C §2.2.3). This is the faithful general measurement — it
carries enough information for **both** the outcome probabilities and the state
update, unlike a bare POVM (which records only the effects `Eᵢ = Mᵢ† Mᵢ`).
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- A **measurement** on the system `S` with outcome
set `ι` is a family of measurement operators `Mᵢ` satisfying the completeness
relation `∑ᵢ Mᵢ† Mᵢ = 1`. -/
structure Measurement (ι : Type*) [Fintype ι] (S : QSystem) where
  /-- The measurement operators. -/
  op : ι → (S →L[ℂ] S)
  /-- Completeness: `∑ᵢ Mᵢ† Mᵢ = 1`. -/
  complete : ∑ i, (adjoint (op i)).comp (op i) = 1

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- The **induced POVM**: outcome `i` has effect `Eᵢ = Mᵢ† Mᵢ`. -/
def toPOVM (m : Measurement ι S) : POVM ι ℂ S where
  elements i := (adjoint (m.op i)).comp (m.op i)
  isPositive i := ContinuousLinearMap.isPositive_adjoint_comp_self (m.op i)
  sum_eq_one := m.complete

@[simp]
theorem toPOVM_elements (m : Measurement ι S) (i : ι) :
    m.toPOVM.elements i = (adjoint (m.op i)).comp (m.op i) := rfl

/-- The **projective measurement in an orthonormal basis** `b`: outcome `i` has measurement
operator the rank-one projector `Mᵢ = |bᵢ⟩⟨bᵢ|`. -/
def ofOrthonormalBasis (b : OrthonormalBasis ι ℂ S) : Measurement ι S where
  op i := rankOne ℂ (b i) (b i)
  complete := by
    rw [ContinuousLinearMap.one_def, ← b.sum_rankOne_eq_id]
    exact Finset.sum_congr rfl fun i _ ↦ adjoint_rankOne_comp_self (b.orthonormal.1 i)

@[simp]
theorem ofOrthonormalBasis_op (b : OrthonormalBasis ι ℂ S) (i : ι) :
    (ofOrthonormalBasis b).op i = rankOne ℂ (b i) (b i) := rfl

/-- **Born rule.** The probability of outcome `i` when measuring `m` on state
`ρ`: `Tr(Mᵢ ρ Mᵢ†) = Tr(Eᵢ ρ)`. -/
def bornProb (m : Measurement ι S) (ρ : State S) (i : ι) : ℝ := m.toPOVM.toPMF ρ.op i

/-- Born probabilities are non-negative. -/
theorem bornProb_nonneg (m : Measurement ι S) (ρ : State S) (i : ι) :
    0 ≤ m.bornProb ρ i :=
  m.toPOVM.toPMF_nonneg ρ.isPositive_op i

/-- **Born rule normalization.** The outcome probabilities sum to one. -/
theorem sum_bornProb_eq_one (m : Measurement ι S) (ρ : State S) :
    ∑ i, m.bornProb ρ i = 1 :=
  m.toPOVM.sum_toPMF_eq_one ρ.isDensity

/-- The Born probability in post-measurement-operation form: `p(i) = re Tr(Mᵢ ρ Mᵢ†)`. -/
theorem bornProb_eq_re_trace_postOp (m : Measurement ι S) (ρ : State S) (i : ι) :
    m.bornProb ρ i =
      RCLike.re (LinearMap.trace ℂ S (ContinuousLinearMap.postOp m.op ρ.op i : S →ₗ[ℂ] S)) := by
  rw [bornProb, POVM.toPMF_eq, ContinuousLinearMap.trace_postOp]
  rfl

/-- **State update (collapse).** The normalized post-measurement
state for outcome `i`, when that outcome is possible (`bornProb ≠ 0`):
`ρ ↦ Mᵢ ρ Mᵢ† / p(i)`. -/
def postMeasurement (m : Measurement ι S) (ρ : State S) (i : ι)
    (hp : m.bornProb ρ i ≠ 0) : State S where
  op := ContinuousLinearMap.postState m.op ρ.op i
  isDensity :=
    ContinuousLinearMap.postState_isDensityOp m.op ρ.isDensity i
      (by rw [← bornProb_eq_re_trace_postOp]; exact hp)

@[simp]
theorem postMeasurement_op (m : Measurement ι S) (ρ : State S) (i : ι)
    (hp : m.bornProb ρ i ≠ 0) :
    (m.postMeasurement ρ i hp).op = ContinuousLinearMap.postState m.op ρ.op i := rfl

end Measurement

end AxQM
