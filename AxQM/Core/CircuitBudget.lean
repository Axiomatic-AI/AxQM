/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledReduction
import AxQM.Basic.API.Associator
import AxQM.Basic.API.SystemIsoComm
import AxQM.Core.TensorPowMultiControlledX
import AxQM.Basic.API.BlockGatePlacement
import AxQM.Core.McNotCircuitEvolution
import AxQM.Basic.API.WirePermutation
import AxQM.Basic.API.Qubit
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import AxQM.Concrete.MultiControlledNotCircuit

/-!
# A compositional elementary-gate budget for `Evolution` circuits (N&C Ex 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`.

## Main declarations
* `CircuitBudget E t s` — the proposition that the `Evolution` `E` is built, up to register
  isomorphism, from **at most `t`** `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`) and **at most `s`**
  single-qubit-controlled gates `C(V)` (`V` a single-qubit gate). It is closed under sequential
  composition (`comp`, budgets add), register transport (`congr`), and weakening (`mono`); its
  leaves are a bottomed `≤ 2`-control block realised by a classical gate list (`block`, contributing
  `gs.length` to `t`), and a single-qubit-controlled gate `C(unCtrl d g)` or its adjoint (`ctrlGate`
  / `ctrlGateAdj`, contributing `1` to `s`). Because no constructor can *lower* a budget,
  `CircuitBudget E t s` is an honest **upper bound** on the elementary-gate count of a realisation.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The elementary-gate budget of an `Evolution` circuit (N&C Ex 4.29).** `CircuitBudget E t s`
holds when `E` is built, up to register isomorphism, from **at most `t`** `≤ 2`-control gates
(`Toffoli`/`CNOT`/`NOT`) and **at most `s`** single-qubit gates — single-qubit-*controlled* gates
`C(V)` (`ctrlGate`/`ctrlGateAdj`) or bare uncontrolled ones (`single`), `V` a single-qubit gate.
Its leaves witness genuine elementary gates, and its structural constructors let the counts of a
composed circuit **add**. No constructor lowers a budget, so `CircuitBudget E t s` is an honest
upper bound on the gate count of a realisation of `E`.

* `block` — a bottomed `≤ 2`-control block: a classical gate list `gs` (each gate `≤ 2` controls,
  target not a control) whose circuit denotation `mcNotDenote gs` is realised by the `Evolution` `U`
  on the flattened register `qubit ^⊗ₛ m`; contributes `gs.length` to the `≤ 2`-control count.
* `ctrlGate` / `ctrlGateAdj` — a single-qubit-controlled gate `C(unCtrl d g)` (resp. its adjoint
  `C((unCtrl d g)†)`), `g : Evolution qubit`, wrapped by `n` idle controls; contributes `1` to the
  single-qubit count.
* `single` — a bare (uncontrolled) single-qubit gate `g : Evolution qubit`, lifted `d` times by idle
  wraps and placed on one wire of a register (`(unCtrl d g).onRight qubit`); contributes `1` to the
  single-qubit count. It is an honest "single qubit gate" in the exercise's sense, so the
  single-qubit count `s` bounds the controlled *and* uncontrolled single-qubit gates together.
* `bare` — a bare single-qubit gate `g : Evolution qubit` on a one-qubit register, with no idle
  wires at all; contributes `1` to the single-qubit count. The degenerate leaf of `single`: the
  register carries no wire to place a gate *on the right of*, and no `unCtrl`/`onRight` wrap can
  shrink a register below one qubit, so it is its own constructor.
* `comp` — sequential composition: budgets add.
* `congr` — transport along a system isomorphism `e : S ≃ₛ T`: budget preserved.
* `mono` — weakening: a budget may be freely increased. -/
inductive CircuitBudget : {S : QSystem} → Evolution S → ℕ → ℕ → Prop where
  | block {m : ℕ} (gs : List (Concrete.McNotGate m)) (U : Evolution (qubit ^⊗ₛ m))
      (hgs : ∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1)
      (hU : ∀ c : Fin m → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) :
      CircuitBudget U gs.length 0
  | ctrlGate {d n : ℕ} (g : Evolution qubit) :
      CircuitBudget (unCtrl n (controlledUnitary (unCtrl d g))) 0 1
  | ctrlGateAdj {d n : ℕ} (g : Evolution qubit) :
      CircuitBudget (unCtrl n (controlledUnitary (unCtrl d g).adjoint)) 0 1
  | single {d : ℕ} (g : Evolution qubit) :
      CircuitBudget ((unCtrl d g).onRight qubit) 0 1
  | bare (g : Evolution qubit) :
      CircuitBudget g 0 1
  | comp {S : QSystem} {E F : Evolution S} {t₁ s₁ t₂ s₂ : ℕ}
      (hE : CircuitBudget E t₁ s₁) (hF : CircuitBudget F t₂ s₂) :
      CircuitBudget (E.comp F) (t₁ + t₂) (s₁ + s₂)
  | congr {S T : QSystem} (e : S.Iso T) {E : Evolution S} {t s : ℕ}
      (h : CircuitBudget E t s) :
      CircuitBudget (Evolution.congr e E) t s
  | mono {S : QSystem} {E : Evolution S} {t s t' s' : ℕ}
      (h : CircuitBudget E t s) (ht : t ≤ t') (hs : s ≤ s') :
      CircuitBudget E t' s'

end AxQM
