/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.HSPQueryState
import AxQM.Basic.API.Purity
import AxQM.Basic.API.HSOverlap
import AxQM.Basic.API.Fidelity
import AxQM.Basic.API.TraceDistance
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import AxQM.Basic.API.CosetDensityState
import AxQM.Basic.API.SquareRootMeasurement
import AxQM.Basic.API.SameNonzeroSpectrum
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumChoi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import AxQM.ToMathlib.Analysis.InnerProductSpace.AlbertiFidelity
import AxQM.ToMathlib.Analysis.InnerProductSpace.Uhlmann
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.Nilpotent
import AxQM.Basic.API.Support
import AxQM.Basic.API.EntropyMixLine

/-!
# Nielsen & Chuang, Problem 5.5 (Non-Abelian hidden subgroups)

*(N&C p. 244.)*

Non-Abelian HSP: prove m=4log|G|+2 coset samples identify K with prob >= 1-1/|G| (research).

* `hspQueryState_reducedLeft_pi_hsOverlap_le_of_sampleCount`
-/

open scoped ComplexOrder

namespace AxQM

variable {G X : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype X] [DecidableEq X]
variable (K : Subgroup G) [DecidablePred (· ∈ K)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### End-to-end identification from N&C's query state (5.80)

N&C, Problem 5.5, says literally: *"Start with the state* (5.80) *… and prove that picking
`m = 4 log|G| + 2` allows `K` to be identified with probability at least `1 − 1/|G|`."*  The
theorems in this block state that conclusion **from the query state (5.80) itself**: the
pretty-good measurement, applied to the reduced state of the `m`-copy query register (5.80),
returns the true hidden subgroup `K` with probability `≥ 1 − 1/|G|`. -/

set_option linter.unusedDecidableInType false in
/-- **N&C Problem 5.5, end-to-end near-orthogonality from the literal query state (5.80), general
`G`, at N&C's exact sample count.**  This is N&C's *stated protocol conclusion* — that
`O(log|G|)` oracle calls leave the outcomes for different hidden subgroups nearly orthogonal —
stated in its **literal** form.

`⟨Tr_X|ψ_f^{⊗m}⟩⟨ψ_f^{⊗m}|, Tr_X|ψ_{f'}^{⊗m}⟩⟨ψ_{f'}^{⊗m}|⟩_HS ≤ 1 / (2|G|²)`,

**for every finite group `G`** (`G` need not be Abelian, no Fourier transform over `G` required)
at N&C's *exact* linear sample count `m = 4 log₂|G| + 2` (the hypothesis `4·|G|⁴ ≤ 2^m`).
-/
theorem hspQueryState_reducedLeft_pi_hsOverlap_le_of_sampleCount (K' : Subgroup G)
    [DecidablePred (· ∈ K')] (f f' : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂)
    (hf' : ∀ g₁ g₂ : G, f' g₁ = f' g₂ ↔ (↑g₁ : G ⧸ K') = ↑g₂)
    (hne : K ≠ K')
    (hm : 4 * (Fintype.card G : ℝ) ^ 4 ≤ (2 : ℝ) ^ Fintype.card ι) :
    ((hspQueryState (fun g : ι → G => fun i => f (g i))).toState.reducedLeft).hsOverlap
        ((hspQueryState (fun g : ι → G => fun i => f' (g i))).toState.reducedLeft)
      ≤ 1 / (2 * (Fintype.card G : ℝ) ^ 2) := sorry

end AxQM
