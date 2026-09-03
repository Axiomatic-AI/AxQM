/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# AxQM — ensembles of pure states and the density operator they generate

An **ensemble of pure states** `{pᵢ, |ψᵢ⟩}` (Nielsen–Chuang §2.4.1) is a finite family of
pure states `|ψᵢ⟩` together with a probability distribution `pᵢ`. Its **density operator**
is the probability-weighted mixture of the pure-state projectors,
`ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` (eq. (2.138)).

## Main definitions

* `AxQM.Ensemble` — an ensemble of pure states: a finite family of `PureState`s with a
  probability distribution.
* `AxQM.Ensemble.toState` — the density operator `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` of an ensemble.

## Main results

* `Ensemble.toState_op` — the `_op` bridge: the ensemble's operator is `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`.
* `isDensityOp_iff_exists_ensemble` — Theorem 2.5, operator form: `T` is a density operator iff it
  is the density operator of some ensemble.
-/

open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- An **ensemble of pure states** `{pᵢ, |ψᵢ⟩}` of a quantum system `S` (Nielsen–Chuang §2.4.1):
a finite family of pure states `states i` together with a probability distribution `prob i`
(non-negative, summing to one). The generating data for a (possibly mixed) density operator. -/
structure Ensemble (S : QSystem) where
  /-- The number of pure states in the ensemble. -/
  card : ℕ
  /-- The probability weights `pᵢ` of the ensemble. -/
  prob : Fin card → ℝ
  /-- The pure states `|ψᵢ⟩` of the ensemble. -/
  states : Fin card → PureState S
  /-- Each probability is non-negative. -/
  prob_nonneg : ∀ i, 0 ≤ prob i
  /-- The probabilities sum to one. -/
  sum_prob : ∑ i, prob i = 1

namespace Ensemble

/-- The **density operator of an ensemble** `{pᵢ, |ψᵢ⟩}` (Nielsen–Chuang eq. (2.138)): the state `ρ
= ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`, the probability-weighted mixture of the pure-state projectors. This is the
*forward* half of Theorem 2.5 — every ensemble yields a genuine density operator — captured by
the target type `State S`. -/
def toState (e : Ensemble S) : State S where
  op := ∑ i, (e.prob i : ℂ) • (e.states i).toState.op
  isDensity := by
    refine ⟨?_, ?_⟩
    · exact ContinuousLinearMap.isPositive_sum _ fun i _ =>
        (e.states i).toState.isPositive_op.smul_of_nonneg (by exact_mod_cast e.prob_nonneg i)
    · rw [ContinuousLinearMap.coe_sum, map_sum]
      simp only [ContinuousLinearMap.coe_smul, map_smul, State.trace_op_eq_one, smul_eq_mul,
        mul_one]
      rw [← Complex.ofReal_sum, e.sum_prob, Complex.ofReal_one]

/-- The **`_op` bridge** for an ensemble's density operator: `ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`, i.e. Nielsen–
Chuang eq. (2.138). Definitional. -/
theorem toState_op (e : Ensemble S) :
    e.toState.op = ∑ i, (e.prob i : ℂ) • (e.states i).toState.op := rfl

end Ensemble

/-- **Nielsen–Chuang Theorem 2.5, operator form.** An operator `T` on a quantum system `S` is a
*density operator* — positive with trace one (`ContinuousLinearMap.IsDensityOp`) — if and only
if it is the density operator `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` of some ensemble of pure states. The literal
rendering of the textbook "ρ is a density operator iff (1) trace one (2) positive": the
`IsDensityOp` predicate is exactly the trace-and-positivity conditions.
-/
theorem isDensityOp_iff_exists_ensemble {T : S →L[ℂ] S} :
    T.IsDensityOp ↔ ∃ e : Ensemble S, e.toState.op = T := sorry

end AxQM
