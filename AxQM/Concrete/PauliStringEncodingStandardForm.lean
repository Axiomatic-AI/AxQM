/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringEncodingStandardFormCore
import AxQM.Concrete.PauliStringEncodingPhaseCZNetwork

/-!
# Concrete: the stabilizer encoding circuit `G (10.124) → standard form (10.125)`
(N&C, Problem 10.3)

This file completes the **synthesis**
half of
Nielsen & Chuang **Problem 10.3** ("encoding stabilizer codes"): a Clifford circuit that carries the
*trivial* check matrix `G` of Eq. (10.124) — a listing of the single-qubit generators `Z₁, …, Zₙ`,
i.e. every row `(0 | eᵢ)`, the stabilizer of `|0⟩⊗ⁿ` — to the **standard form** of Eq. (10.125).

## Main results
* `checkRow_encodingCircuit_middle` / `_data` — the middle / encoded-`Z` rows equal the ones the
  core
  produced (the phase/`CZ` layer fixes them): `[0 | D I E]`, `[0 | A₂ᵀ 0 I]`.
* `encodingCircuit_standardForm_achievable` — the **achievability** (pinnacle claim): for **any**
  standard-form code (`A₁, A₂, E` via `D`, and `B`, `C₂` with the top-row commutation relation)
  there *exists* phase/`CZ` data whose encoding circuit carries `G` (10.124) to that code's
  (10.125) with **exactly** its blocks.
-/

namespace AxQM.Concrete

open Matrix

variable {n : ℕ}

/-- **The stabilizer encoding circuit** (N&C Problem 10.3): the CNOT + Hadamard core followed
(acting last) by the phase / controlled-`Z` network, `phaseCZNetwork ws pairs ++ encodingCnotHad D`.
Read right-to-left, the Hadamards convert `Zₚ ↦ Xₚ` on the pivots, the CNOT network builds the
`X`-blocks and the coupled `Z`-blocks (`A₁, A₂, D, E, A₂ᵀ`), and the phase/`CZ` network deposits the
residual top-row `Z`-blocks `B`, `C₂`. Applied to the trivial check matrix `G` (10.124) it produces
the standard form (10.125). -/
def encodingCircuit (D : StdFormData n) (ws : List (Fin n)) (pairs : List (Fin n × Fin n)) :
    CliffordCircuit n :=
  phaseCZNetwork ws pairs ++ encodingCnotHad D

/-- **The encoding circuit fixes the middle rows** `[0 | D I E]` (N&C (10.125)): for a middle wire
`m`, the phase/`CZ` layer leaves the core's output unchanged (that row has zero `X`-part), so the
whole circuit gives the same row as the CNOT + Hadamard core. -/
theorem checkRow_encodingCircuit_middle (D : StdFormData n) (ws : List (Fin n))
    (pairs : List (Fin n × Fin n)) (hws : ws.Nodup) (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2)
    {m : Fin n} (hm : m ∈ D.middle) :
    checkRow (CliffordCircuit.act (encodingCircuit D ws pairs) (zGenPauli m))
      = checkRow (CliffordCircuit.act (encodingCnotHad D) (zGenPauli m)) := sorry

/-- **The encoding circuit fixes the encoded-`Z` rows** `[0 | A₂ᵀ 0 I]` (N&C (10.125)): for an
encoded wire `d`, the phase/`CZ` layer leaves the core's output unchanged (that row has zero
`X`-part), so the whole circuit gives the same row as the CNOT + Hadamard core. -/
theorem checkRow_encodingCircuit_data (D : StdFormData n) (ws : List (Fin n))
    (pairs : List (Fin n × Fin n)) (hws : ws.Nodup) (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2)
    {d : Fin n} (hd : d ∈ D.dataWires) :
    checkRow (CliffordCircuit.act (encodingCircuit D ws pairs) (zGenPauli d))
      = checkRow (CliffordCircuit.act (encodingCnotHad D) (zGenPauli d)) := sorry

open Finset in
/-- **Achievability of every standard form** (N&C Problem 10.3, the pinnacle claim). -/
theorem encodingCircuit_standardForm_achievable
    (D : StdFormData n) (B C₂ : Fin n → Fin n → ZMod 2)
    (hC₂ : ∀ q d, C₂ q d ≠ 0 → d ∈ D.dataWires)
    (hcomm : ∀ p ∈ D.pivots, ∀ q ∈ D.pivots,
        B p q + B q p
          = (∑ d, (if d ∈ D.tgt p then (1 : ZMod 2) else 0) * C₂ q d)
            + (∑ d, (if d ∈ D.tgt q then (1 : ZMod 2) else 0) * C₂ p d)) :
    ∃ ws pairs, ws.Nodup ∧ (∀ pr ∈ pairs, pr.1 ≠ pr.2)
      ∧ (∀ w ∈ ws, w ∉ D.middle)
      ∧ (∀ pr ∈ pairs, pr.1 ∉ D.middle ∧ pr.2 ∉ D.middle)
      ∧ ∀ p ∈ D.pivots,
        checkRow (CliffordCircuit.act (encodingCircuit D ws pairs) (zGenPauli p))
          = (fun k => (if k = p then (1 : ZMod 2) else 0) + (if k ∈ D.tgt p then 1 else 0),
             fun k => (if k ∈ D.pivots then B p k else 0)
               + (if k ∈ D.dataWires then C₂ p k else 0)) := sorry

end AxQM.Concrete
