/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuditGate
import AxQM.Basic.API.QuditTensorFactor
import AxQM.Basic.API.Associator
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.DeutschGate
import AxQM.Basic.API.LeftPairGate
import AxQM.Concrete.DeutschDoublyControlledReachable
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# Register identification for the three-qubit ↔ eight-level register (N&C Ex 4.44 physics lift)

This file supplies the ** register identification** for expressing the physical
Deutsch gate `deutschGate α = ccontrolledUnitary (iRxGate (πα))` (a gate on the composite
three-qubit system `qubit ⊗ qubit ⊗ qubit`) as an explicit matrix on the eight-level register
`qudit 8` —
the representation in which the whole matrix reachability/compression layer of Exercise 4.44
(`Concrete.deutschWirePlacedReachable`, `…deutschDataReachableCircuits`, etc.) lives.

## Main declarations
* `threeQuditIso` — the system isomorphism `qudit 2 ⊗ (qudit 2 ⊗ qudit 2) ≃ₛ qudit 8`, built from
  the tensor-factoring isomorphism `quditProdIso` (splitting `qudit 8 ≃ qudit 2 ⊗ qudit 4` and then
  `qudit 4 ≃ qudit 2 ⊗ qudit 2`). As `qubit = qudit 2` definitionally, any evolution on
  `qubit ⊗ (qubit ⊗ qubit)` — in particular `deutschGate α` — transports along it.
-/

namespace AxQM

open scoped TensorProduct

noncomputable section

/-- The system isomorphism `qudit 2 ⊗ (qudit 2 ⊗ qudit 2) ≃ₛ qudit 8` (identifying the three-qubit
register with the eight-level register). As `qubit = qudit 2` definitionally, an evolution on
`qubit ⊗ (qubit ⊗ qubit)` — such as `deutschGate α` — transports along it. It is built from the
tensor-factoring isomorphism `quditProdIso`, splitting `qudit 8 ≃ qudit 2 ⊗ qudit 4` and the right
`qudit 4 ≃ qudit 2 ⊗ qudit 2`. -/
def threeQuditIso : ((qudit 2) ⊗ ((qudit 2) ⊗ (qudit 2))) ≃ₛ qudit 8 :=
  (QSystem.Iso.tmul (QSystem.Iso.refl (qudit 2)) (quditProdIso 2 2).symm).trans
    (quditProdIso 2 4).symm

end

end AxQM
