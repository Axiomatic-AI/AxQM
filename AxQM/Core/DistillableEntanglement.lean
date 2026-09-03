/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.MaxEntMarginal
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.TensorPowState
import AxQM.Basic.PiTensor
import AxQM.Basic.API.Qubit
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Free
import AxQM.Basic.API.StateMajorization
import AxQM.Basic.API.TraceDistance

/-!
# AxQM — the asymptotic entanglement-distillation rate framework

The framework behind **entanglement distillation** (N&C §12.5.2): the achievable-rate predicate
`IsDistillationRate` and the operational `distillableEntanglement := sSup` of achievable rates.
-/

noncomputable section

open Filter Topology

namespace AxQM

variable {S : QSystem}

/-- **An achievable entanglement-distillation rate** (N&C §12.5.2). A real `R` (in *nats* of
entanglement per copy) is achievable for the marginal `ρ` if there is a family of LOCC protocols
that, from `ρ^⊗m` (Alice's marginal of `m` copies of `|ψ⟩`), produce outputs `σ_m` converging in
trace distance (fidelity → 1) to genuine rank-`K_m` maximally entangled marginals `μ_m`, with the
extraction rate `log (K_m) / m → R`.

The `μ_m` pin the target to *actual* `K_m`-dimensional maximal entanglement (`IsMaxEntMarginal`), so
this captures LOCC extraction of Bell-type resources, not merely production of a high-entropy state.
For `K_m = 2ⁿ` the target is `n` Bell pairs. -/
def IsDistillationRate (ρ : State S) (R : ℝ) : Prop :=
  ∃ (K : ℕ → ℕ) (σ μ : (m : ℕ) → State (S.tensorPow m)),
    (∀ m, (ρ.tensorPow m).LOCCConvertible (σ m)) ∧
    (∀ m, (μ m).IsMaxEntMarginal (K m)) ∧
    Tendsto (fun m => (σ m).traceDistance (μ m)) atTop (𝓝 0) ∧
    Tendsto (fun m => Real.log (K m) / m) atTop (𝓝 R)

/-- **The distillable entanglement** `D(ρ)` (N&C §12.5.2): the supremum of all achievable
distillation rates. For the marginal `ρ_ψ` of a bipartite pure state `|ψ⟩`, `D(ρ_ψ)` is the
operational amount of entanglement (in nats) extractable from `|ψ⟩` as Bell states by LOCC. -/
def distillableEntanglement (ρ : State S) : ℝ :=
  sSup {R | IsDistillationRate ρ R}

end AxQM
