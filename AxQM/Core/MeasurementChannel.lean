/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Qudit
import AxQM.Basic.API.Mixture
import AxQM.Basic.API.ArakiLiebEqualityConditions
import AxQM.Basic.API.RelativeEntropy
import AxQM.Basic.API.QuditMeasurement
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy

/-!
# AxQM — the POVM measurement outcome channel

The **measurement outcome channel** of a measurement `m : Measurement ι S`: the map sending a
state `ρ` of `S` to the *diagonal Born-distribution state* of a classical outcome register.
-/

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- The **measurement outcome channel** `𝓜(ρ) = ∑_y Tr(E_y ρ) |y⟩⟨y|` of a measurement `m :
Measurement ι S`: the state of the classical outcome register `qudit (Fintype.card ι)` whose
`|y⟩⟨y|` weight is the Born probability of outcome `y`. -/
def measState (m : Measurement ι S) (ρ : State S) : State (qudit (Fintype.card ι)) :=
  State.mix (m.bornProb ρ) (m.bornProb_nonneg ρ) (m.sum_bornProb_eq_one ρ)
    (fun i => (quditBasis (Fintype.equivFin ι i)).toState)

end Measurement

end AxQM
