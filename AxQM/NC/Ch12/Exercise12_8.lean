/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.Theorem12_5
import AxQM.Basic.API.Fidelity
import AxQM.Basic.API.TraceDistance
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
import AxQM.Concrete.ClassicalTraceDistance
import AxQM.Basic.API.QuantumChannel
import AxQM.Basic.API.Ensemble
import AxQM.ToMathlib.Analysis.InnerProductSpace.EntanglementFidelity
import AxQM.Basic.API.EnsembleIidPow
import AxQM.NC.Ch9.Exercise9_23

/-!
# N&C Exercise 12.8 — compression of an ensemble of quantum states

*(N&C p. 546.)*

Ensemble-fidelity compression: show reliable rate R > S(rho) for ensemble source.

* `exists_reliable_ensembleCompression`
-/

open scoped InnerProductSpace ComplexOrder Topology BigOperators
open ContinuousLinearMap InnerProductSpace Filter

noncomputable section

namespace AxQM

variable {T : QSystem}

/-- **Nielsen & Chuang Exercise 12.8** (compression of an ensemble of quantum states): for an
ensemble source `e = {pⱼ, |ψⱼ⟩}` with average density operator `ρ = e.toState = ∑ⱼ pⱼ |ψⱼ⟩⟨ψⱼ|`,
**provided `R > S(ρ)` there exists a reliable compression scheme of rate `R`** in the
ensemble-average-fidelity sense (Eq. 12.61).

Concretely: for `R > ρ.vonNeumannEntropy` there is an `ε > 0` and a family of maps
`C : ∀ n, State (T ^⊗ₛ n) → State (T ^⊗ₛ n)` such that

* every `C n` is a genuine quantum channel (`IsChannel (C n)`);
* **rate `R`**: the code dimension `|T(n, ε)| = ρ.typicalSubspaceDim n ε` satisfies
  `|T(n, ε)| ≤ exp(n · R)` (nats; N&C's `2^{nR}`) for all sufficiently large `n`;
* **compression into that code**: for all sufficiently large `n`, every output `C n σ` lies in the
  `|T(n, ε)|`-dimensional typical subspace, `(ρ.typicalSubspaceMeasurement n ε).bornProb (C n σ)
  true = 1` — this couples the channel to the rate bound (the non-compressing identity family is
  excluded);
* **reliability**: the ensemble average fidelity
  `∑_J p_J · F(ρ_J, C n (ρ_J))² = ensembleAvgFidelity (e.iidPow n).prob (fun J ↦ ρ_J) (C n)`
  of `C n` over the `n`-fold i.i.d. source `e.iidPow n` tends to `1` as `n → ∞`. -/
theorem exists_reliable_ensembleCompression (e : Ensemble T) {R : ℝ}
    (hR : e.toState.vonNeumannEntropy < R) :
    ∃ (ε : ℝ) (C : (n : ℕ) → State (T ^⊗ₛ n) → State (T ^⊗ₛ n)),
      0 < ε ∧ (∀ n, IsChannel (C n)) ∧
      (∀ᶠ n in atTop, (e.toState.typicalSubspaceDim n ε : ℝ) ≤ Real.exp (n * R)) ∧
      (∀ᶠ n in atTop, ∀ σ, (e.toState.typicalSubspaceMeasurement n ε).bornProb (C n σ) true = 1) ∧
      Tendsto (fun n => ensembleAvgFidelity (e.iidPow n).prob
        (fun J => ((e.iidPow n).states J).toState) (C n)) atTop (𝓝 1) := sorry

end AxQM
