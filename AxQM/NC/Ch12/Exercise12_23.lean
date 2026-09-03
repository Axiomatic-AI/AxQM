/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.DistillableEntanglement
import AxQM.Basic.API.StateMajorization
import AxQM.Basic.API.RelativeEntropy
import AxQM.Basic.API.Mixture
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.RandomUnitaryChannel
import AxQM.Basic.API.TensorPowSplit
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.EntropyComposite
import AxQM.Basic.API.TensorPowState
import AxQM.Basic.PiTensor
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Free
import AxQM.NC.Ch11.Theorem11_6

/-!
# Nielsen–Chuang, Exercise 12.23 — the entanglement distillation procedure is optimal

*(N&C p. 580.)*

Prove the described entanglement distillation procedure is optimal.

* `distillableEntanglement_reducedLeft_le` — for a bipartite pure state `ψ`:
  `distillableEntanglement ρ_ψ ≤ S(ρ_ψ)`.
-/

noncomputable section

open Filter Topology

namespace AxQM

variable {S : QSystem}

/-- **Optimality of distillation for a bipartite pure state** (N&C Exercise 12.23): for a
bipartite pure state `|ψ⟩`, the distillable entanglement of its reduced state
`ρ_ψ` is at most the entanglement entropy `S(ρ_ψ)`,

`distillableEntanglement ρ_ψ ≤ S(ρ_ψ)`.

Together with N&C's achievability (§12.5.2, the typical-subspace procedure attains `S(ρ_ψ)`),
this says the described distillation procedure is optimal: the distillable entanglement equals
`S(ρ_ψ)`.
-/
theorem PureState.distillableEntanglement_reducedLeft_le {T : QSystem}
    (ψ : PureState (S.compose T)) :
    distillableEntanglement ψ.toState.reducedLeft ≤ ψ.toState.reducedLeft.vonNeumannEntropy := sorry

end AxQM
