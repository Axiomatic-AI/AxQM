/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EntropyJointTheorem
import AxQM.Basic.API.MutualInformation
import AxQM.Basic.API.ArakiLiebEqualityConditions
import AxQM.Basic.API.Qudit
import AxQM.Basic.PartialTrace
import AxQM.Basic.Composite
import AxQM.Basic.API.RelativeEntropy
import AxQM.Basic.API.Mixture
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.EntropyComposite

/-!
# AxQM — the Holevo χ quantity

The **Holevo χ quantity** of an ensemble `{pₓ, ρₓ}` of quantum states (Nielsen & Chuang,
eq. (12.208)).
-/

noncomputable section

namespace AxQM

variable {S : QSystem} {ι : Type*} [Fintype ι]
  (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)

/-- The **Holevo χ quantity** of an ensemble `{pᵢ, ρᵢ}` (Nielsen & Chuang, eq. (12.208)):
`χ = S(∑ᵢ pᵢ ρᵢ) − ∑ᵢ pᵢ S(ρᵢ)`, the entropy of the mixture minus the average component entropy. -/
def State.holevoChi : ℝ :=
  (State.mix p hp hsum ρ).vonNeumannEntropy - ∑ i, p i * (ρ i).vonNeumannEntropy

end AxQM
