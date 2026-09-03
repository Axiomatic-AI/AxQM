/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CascadedMeasurement

/-!
# Nielsen & Chuang, Exercise 2.57 (cascaded measurements are single measurements)

*(N&C p. 86.)*

Show cascaded measurements {L_l} then {M_m} equal single measurement N_lm=M_m L_l.

* `cascade_bornProb` — the joint outcome probability factorizes as `p(l, m) = p(l) · p(m ∣ l)`: the
  cascade's Born probability for outcome `(l, m)` equals the probability of `l` under `L` times the
  probability of `m` under `M` *in the state left by `L`'s outcome `l`*.
* `cascade_postMeasurement` — the post-measurement states agree: collapsing under the single
  measurement `N` for outcome `(l, m)` yields the same `State` as collapsing under `L` (outcome `l`)
  and then under `M` (outcome `m`).
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {κ μ : Type*} [Fintype κ] [Fintype μ] {S : QSystem}

/-- **Cascaded measurements: probabilities chain (N&C Exercise 2.57).** The Born probability of
the single cascade measurement `L.cascade M` for the joint outcome `(l, m)` equals the probability
`p(l)` of outcome `l` under `L` times the probability `p(m ∣ l)` of outcome `m` under `M` computed
in the post-measurement state `L.postMeasurement ρ l` — the chained probability
`p(l, m) = p(l) · p(m ∣ l)` of measuring `L` and then `M`. -/
theorem cascade_bornProb (L : Measurement κ S) (M : Measurement μ S) (ρ : State S)
    (l : κ) (m : μ) (hl : L.bornProb ρ l ≠ 0) :
    (L.cascade M).bornProb ρ (l, m)
      = L.bornProb ρ l * M.bornProb (L.postMeasurement ρ l hl) m := by
  have hp : RCLike.re (LinearMap.trace ℂ S
      (ContinuousLinearMap.postOp L.op ρ.op l : S →ₗ[ℂ] S)) ≠ 0 := by
    rw [← Measurement.bornProb_eq_re_trace_postOp]; exact hl
  -- `p(m ∣ l)`, unfolded: measuring `M` on `Eₗ(ρ)/p(l)` gives `Tr(Mₘ Lₗ ρ Lₗ† Mₘ†) / p(l)`.
  have key : M.bornProb (L.postMeasurement ρ l hl) m
      = (RCLike.re (LinearMap.trace ℂ S (ContinuousLinearMap.postOp L.op ρ.op l : S →ₗ[ℂ] S)))⁻¹
        * RCLike.re (LinearMap.trace ℂ S
            (ContinuousLinearMap.postOp M.op (ContinuousLinearMap.postOp L.op ρ.op l) m
              : S →ₗ[ℂ] S)) := by
    rw [Measurement.bornProb_eq_re_trace_postOp, Measurement.postMeasurement_op,
      ContinuousLinearMap.postState, ContinuousLinearMap.postOp_smul, ContinuousLinearMap.coe_smul,
      map_smul, smul_eq_mul]
    simp
  rw [Measurement.bornProb_eq_re_trace_postOp (L.cascade M), Measurement.postOp_cascade,
    Measurement.bornProb_eq_re_trace_postOp L, key, mul_inv_cancel_left₀ hp]

/-- **Cascaded measurements: states chain (N&C Exercise 2.57).** The post-measurement `State` of the
single cascade measurement `L.cascade M` for the joint outcome `(l, m)` equals the state
obtained by collapsing first under `L` (outcome `l`) and then under `M` (outcome `m`): `N₍ₗ,ₘ₎ ρ
N₍ₗ,ₘ₎† / p(l, m) = Mₘ (Lₗ ρ Lₗ† / p(l)) Mₘ† / p(m ∣ l)`. -/
theorem cascade_postMeasurement (L : Measurement κ S) (M : Measurement μ S) (ρ : State S)
    (l : κ) (m : μ) (hl : L.bornProb ρ l ≠ 0)
    (hm : M.bornProb (L.postMeasurement ρ l hl) m ≠ 0) :
    (L.cascade M).postMeasurement ρ (l, m)
        (by rw [cascade_bornProb L M ρ l m hl]; exact mul_ne_zero hl hm)
      = M.postMeasurement (L.postMeasurement ρ l hl) m hm := sorry

end AxQM
