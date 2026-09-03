/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.McNotCircuitEvolution
import AxQM.Concrete.MultiControlledNotCircuit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Defs

/-!
# Nielsen & Chuang, Exercise 10.26 — computing a parity-check syndrome with CNOTs

*(N&C p. 451.)*

Explain how to compute |x>|0> -> |x>|Hx> using a circuit of controlled-NOTs.

* `exists_cnotEvolution_paritySyndrome`
-/

noncomputable section

namespace AxQM

/-- **N&C Exercise 10.26: a CNOT circuit computing the parity-check syndrome.** For any parity-check
matrix `H : Fin k → Fin n → Fin 2`, there is a **gate list** `gs` and a unitary `Evolution U` on the
`n + k`-qubit register `qubit ^⊗ₛ (n + k)` (`n` data qubits, `k` syndrome ancillas) such that:
* every gate of `gs` is a genuine single-control controlled-NOT — control set of size one, target
  off it (`g.1.card = 1 ∧ g.2 ∉ g.1`): the circuit is *composed entirely of controlled-NOTs*;
* `U` is exactly the closed-system realisation of that circuit — it acts on every computational
  basis state `⨂ᵢ |c i⟩` by the circuit's classical denotation `Concrete.mcNotDenote gs`;
* `U` sends `|x⟩|0⟩` to `|x⟩|Hx⟩`, the syndrome `(Hx)ᵢ = ∑ⱼ H i j · xⱼ` computed mod 2 in the
  ancillas. -/
theorem exists_cnotEvolution_paritySyndrome {n k : ℕ} (H : Fin k → Fin n → Fin 2) :
    ∃ (gs : List (Concrete.McNotGate (n + k))) (U : Evolution (qubit ^⊗ₛ (n + k))),
      (∀ g ∈ gs, g.1.card = 1 ∧ g.2 ∉ g.1) ∧
      (∀ c : Fin (n + k) → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i))
          = PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      ∀ x : Fin n → Fin 2,
        U.evolvePure (PureState.piTensor fun w => qubitBasis (Fin.append x (fun _ => 0) w))
          = PureState.piTensor fun w =>
            qubitBasis (Fin.append x (fun i => ∑ j, H i j * x j) w) := sorry

end AxQM
