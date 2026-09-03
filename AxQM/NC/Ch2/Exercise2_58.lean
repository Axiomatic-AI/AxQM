/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Variance

/-!
# Nielsen & Chuang, Exercise 2.58

*(N&C p. 88.)*

For an eigenstate of observable M, find the average value and standard deviation.

* `eigenstate_expectation_eq_eigenvalue` — the average is the eigenvalue: if `ψ` is an eigenstate of
  `M` with eigenvalue `m`, then `⟪M⟫_ψ = m`.
* `eigenstate_stdDev_eq_zero` — the standard deviation vanishes: in the same situation `Δ(M)_ψ = 0`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 2.58 (average).** If the pure state `ψ` is an eigenstate of the
observable `M` with eigenvalue `m`, then the average observed value of `M` is the eigenvalue:
`⟪M⟫_ψ = m`. The measurement of `M` in an eigenstate returns `m` with certainty, so its mean
is `m`. -/
theorem eigenstate_expectation_eq_eigenvalue {ψ : PureState S} {M : Observable S} {m : ℝ}
    (h : M.HasEigenstate m ψ) : ψ.expectation M = m := sorry

/-- **Nielsen & Chuang, Exercise 2.58 (standard deviation).** If the pure state `ψ` is an eigenstate
of the observable `M` with eigenvalue `m`, then the standard deviation of `M` vanishes: `Δ(M)_ψ
= 0`. There is no spread in the measured values, since `M` yields `m` with certainty. -/
theorem eigenstate_stdDev_eq_zero {ψ : PureState S} {M : Observable S} {m : ℝ}
    (h : M.HasEigenstate m ψ) : ψ.stdDev M = 0 := sorry

end AxQM
