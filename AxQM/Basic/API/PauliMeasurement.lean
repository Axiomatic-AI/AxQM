/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PureState
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.Measurement

/-!
# AxQM.Basic.API — projective measurement of a `±1` observable, and `v · σ` on `|0⟩`

The infrastructure behind Nielsen & Chuang Exercises 2.60–2.61: the **projective
measurement of an observable whose square is the identity** (a self-adjoint involution, eigenvalues
`±1`), and its specialization to the Pauli vector observable `v · σ` measured on the computational
basis state `|0⟩`.
-/

open scoped InnerProductSpace Matrix
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Observable

/-- The **`+1` eigenprojector** `P₊ = (I + A)/2` of an observable `A` (N&C Exercise 2.60). A genuine
projector exactly when `A² = I`. -/
def projPlus (A : Observable S) : S →L[ℂ] S := (2⁻¹ : ℂ) • (1 + A.op)

/-- The **`−1` eigenprojector** `P₋ = (I − A)/2` of an observable `A` (N&C Exercise 2.60). -/
def projMinus (A : Observable S) : S →L[ℂ] S := (2⁻¹ : ℂ) • (1 - A.op)

/-- `P₊` is self-adjoint. -/
theorem projPlus_isSelfAdjoint (A : Observable S) : IsSelfAdjoint A.projPlus := by
  rw [projPlus, IsSelfAdjoint, star_smul, star_add, star_one, A.selfAdjoint.star_eq]
  norm_num

/-- `P₋` is self-adjoint. -/
theorem projMinus_isSelfAdjoint (A : Observable S) : IsSelfAdjoint A.projMinus := by
  rw [projMinus, IsSelfAdjoint, star_smul, star_sub, star_one, A.selfAdjoint.star_eq]
  norm_num

/-- `adjoint P₊ = P₊` (self-adjointness in operator form). -/
theorem adjoint_projPlus (A : Observable S) : adjoint A.projPlus = A.projPlus := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact A.projPlus_isSelfAdjoint

/-- `adjoint P₋ = P₋`. -/
theorem adjoint_projMinus (A : Observable S) : adjoint A.projMinus = A.projMinus := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact A.projMinus_isSelfAdjoint

/-- For an involution `A² = I`, the `+1` eigenprojector is **idempotent**: `P₊² = P₊`. -/
theorem projPlus_mul_self (A : Observable S) (hinv : A.op * A.op = 1) :
    A.projPlus * A.projPlus = A.projPlus := by
  have hB : (1 + A.op) * (1 + A.op) = (2 : ℂ) • (1 + A.op) := by
    rw [two_smul, mul_add, add_mul, add_mul]
    simp only [mul_one, one_mul, hinv]; abel
  rw [projPlus, smul_mul_smul_comm, hB, smul_smul]
  norm_num

/-- For an involution `A² = I`, the `−1` eigenprojector is idempotent: `P₋² = P₋`. -/
theorem projMinus_mul_self (A : Observable S) (hinv : A.op * A.op = 1) :
    A.projMinus * A.projMinus = A.projMinus := by
  have hB : (1 - A.op) * (1 - A.op) = (2 : ℂ) • (1 - A.op) := by
    rw [two_smul, mul_sub, sub_mul, sub_mul]
    simp only [mul_one, one_mul, hinv]; abel
  rw [projMinus, smul_mul_smul_comm, hB, smul_smul]
  norm_num

/-- The eigenprojectors resolve the identity: `P₊ + P₋ = I`. -/
theorem projPlus_add_projMinus (A : Observable S) : A.projPlus + A.projMinus = 1 := by
  rw [projPlus, projMinus, ← smul_add]
  rw [show (1 + A.op) + (1 - A.op) = (2 : ℂ) • (1 : S →L[ℂ] S) by rw [two_smul]; abel, smul_smul]
  norm_num

/-- The **projective measurement of a `±1` observable** `A` (an involution `A² = I`): the
two-outcome measurement with operators `M₀ = P₊`, `M₁ = P₋` (outcome `0 ↔ +1`, `1 ↔ −1`). This is
the projective measurement of the observable `A` (N&C §2.2.5); its `+1` outcome is Exercise
2.61. -/
def signMeasurement (A : Observable S) (hinv : A.op * A.op = 1) : Measurement (Fin 2) S where
  op := ![A.projPlus, A.projMinus]
  complete := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      A.adjoint_projPlus, A.adjoint_projMinus, ← ContinuousLinearMap.mul_def,
      A.projPlus_mul_self hinv, A.projMinus_mul_self hinv]
    exact A.projPlus_add_projMinus

@[simp]
theorem signMeasurement_op_zero (A : Observable S) (hinv : A.op * A.op = 1) :
    (A.signMeasurement hinv).op 0 = A.projPlus := rfl

@[simp]
theorem signMeasurement_op_one (A : Observable S) (hinv : A.op * A.op = 1) :
    (A.signMeasurement hinv).op 1 = A.projMinus := rfl

/-- The post-measurement operation for the `+1` outcome sends `|ψ⟩⟨ψ|` to the rank-one operator
`|P₊ψ⟩⟨P₊ψ|`. -/
theorem postOp_signMeasurement_zero (A : Observable S) (hinv : A.op * A.op = 1) (ψ : PureState S) :
    ContinuousLinearMap.postOp (A.signMeasurement hinv).op ψ.toState.op 0
      = rankOne ℂ (A.projPlus ψ.vec) (A.projPlus ψ.vec) := by
  simp only [ContinuousLinearMap.postOp, signMeasurement_op_zero, PureState.toState_op,
    A.adjoint_projPlus, InnerProductSpace.comp_rankOne, InnerProductSpace.rankOne_comp]

/-- **Born probability of `+1` as a squared norm:** `p(+1) = ‖P₊|ψ⟩‖²`. -/
theorem bornProb_signMeasurement_plus_eq_normSq (A : Observable S) (hinv : A.op * A.op = 1)
    (ψ : PureState S) :
    (A.signMeasurement hinv).bornProb ψ.toState 0 = ‖A.projPlus ψ.vec‖ ^ 2 := by
  rw [Measurement.bornProb_eq_re_trace_postOp, postOp_signMeasurement_zero,
    InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq]

/-- If the `+1` outcome is possible (`p(+1) ≠ 0`), then `P₊|ψ⟩ ≠ 0` — the post-measurement state is
well-defined. -/
theorem projPlus_apply_ne_zero_of_bornProb (A : Observable S) (hinv : A.op * A.op = 1)
    (ψ : PureState S) (hp : (A.signMeasurement hinv).bornProb ψ.toState 0 ≠ 0) :
    A.projPlus ψ.vec ≠ 0 := by
  intro h0
  exact hp (by rw [bornProb_signMeasurement_plus_eq_normSq, h0, norm_zero]; norm_num)

/-- The **normalized `+1` post-measurement pure state** `P₊|ψ⟩ / ‖P₊|ψ⟩‖` — the collapsed state
after the `±1` measurement of `A` yields `+1`, defined when `P₊|ψ⟩ ≠ 0` (i.e. when `+1`
is a possible outcome). It is the `+1` eigenstate of `A`. -/
def postMeasPlus (A : Observable S) (ψ : PureState S) (hne : A.projPlus ψ.vec ≠ 0) :
    PureState S :=
  PureState.normalize (A.projPlus ψ.vec) hne

end Observable

/-- **The `±1` eigenvalue selected by a bit `s`** under the sign-measurement convention: `+1` for
`s = 0`, `−1` for `s = 1` (i.e. `(-1)^s`); `s` is the `Fin 2` index of the corresponding
`Observable.signMeasurement` outcome (`0 ↔ +1`, `1 ↔ −1`). -/
def signEigenvalue : Fin 2 → ℝ := ![1, -1]

end AxQM
