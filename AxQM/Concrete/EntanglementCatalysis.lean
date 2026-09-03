/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.ToMathlib.Analysis.Convex.Majorization

/-!
# Entanglement catalysis — the majorization data

Nielsen & Chuang, Exercise 12.21, exhibits *entanglement catalysis*: `|ψ⟩` cannot be taken to
`|φ⟩` by LOCC, but `|ψ⟩|c⟩` can be taken to `|φ⟩|c⟩`.

## Main definitions

* `catalysisPsiSpec`, `catalysisPhiSpec` : `Fin 4 → ℝ`, and `catalysisCatSpec` : `Fin 2 → ℝ` — the
  three squared-Schmidt spectra (exact rationals). Each is a probability vector
  (`_nonneg`, `_sum_eq_one`).
-/

open Finset

namespace AxQM.Concrete

/-- Squared Schmidt coefficients of `|ψ⟩ = √0.4|00⟩ + √0.4|11⟩ + √0.1|22⟩ + √0.1|33⟩`, the source
state of the catalysis example: `λ_ψ = (0.4, 0.4, 0.1, 0.1)`. -/
noncomputable def catalysisPsiSpec : Fin 4 → ℝ := ![2/5, 2/5, 1/10, 1/10]

/-- Squared Schmidt coefficients of `|φ⟩ = √0.5|00⟩ + √0.25|11⟩ + √0.25|22⟩`, the target state of
the catalysis example: `λ_φ = (0.5, 0.25, 0.25, 0)`. -/
noncomputable def catalysisPhiSpec : Fin 4 → ℝ := ![1/2, 1/4, 1/4, 0]

/-- Squared Schmidt coefficients of the catalyst `|c⟩ = √0.6|00⟩ + √0.4|11⟩`:
`λ_c = (0.6, 0.4)`. -/
noncomputable def catalysisCatSpec : Fin 2 → ℝ := ![3/5, 2/5]

lemma catalysisPsiSpec_nonneg (i : Fin 4) : 0 ≤ catalysisPsiSpec i := by
  fin_cases i <;> simp [catalysisPsiSpec] <;> norm_num

lemma catalysisPhiSpec_nonneg (i : Fin 4) : 0 ≤ catalysisPhiSpec i := by
  fin_cases i <;> simp [catalysisPhiSpec]

lemma catalysisCatSpec_nonneg (i : Fin 2) : 0 ≤ catalysisCatSpec i := by
  fin_cases i <;> simp [catalysisCatSpec] <;> norm_num

lemma catalysisPsiSpec_sum_eq_one : ∑ i, catalysisPsiSpec i = 1 := by
  simp [catalysisPsiSpec, Fin.sum_univ_four]; norm_num

lemma catalysisPhiSpec_sum_eq_one : ∑ i, catalysisPhiSpec i = 1 := by
  simp [catalysisPhiSpec, Fin.sum_univ_four]; norm_num

lemma catalysisCatSpec_sum_eq_one : ∑ i, catalysisCatSpec i = 1 := by
  simp [catalysisCatSpec, Fin.sum_univ_two]; norm_num

end AxQM.Concrete
