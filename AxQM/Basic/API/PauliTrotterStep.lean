/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliTrotterSummand
import AxQM.Basic.API.PauliTrotter

/-!
# One full Trotter step `∏_g exp(-i h_g g Δ)` over all `4ⁿ` Pauli strings (N&C Problem 4.3(6))

Nielsen & Chuang, Problem 4.3(6) assembles the universal approximation `U ≈ [∏_g exp(-i h_g g Δ)]ᵏ`
as the `k`-fold power (part (5)) of **one Trotter step** — the ordered product, over *all* `4ⁿ`
Pauli strings `g : Fin n → Fin 4`, of the summands `exp(-i h_g g Δ)`. Parts (2)–(5) of Problem 4.3
already prove that this operator product is `O(Δ²)`-close to `exp(-i H Δ)` and its `k`-fold power
`O(1/k)`-close to `U`. Those bounds are stated over the
**operator** product `∏_g ((pauliStringHamiltonian g (h g)).propagator 1 0 Δ).op`; part (6)
additionally needs the **circuit** — a single `Evolution` — whose *gate count* can be bounded, and
whose operator *is* that product. This file supplies that circuit.

## Main declarations
* `pauliTrotterStep n h t` — **one full Trotter step** `∏_g exp(-i h_g g t)`, as one
  `Evolution (qudit (2ⁿ))`: the ordered product `(Finset.univ.toList.map fun g =>
  pauliTrotterSummand n g (h g) t).prod` of the total per-string summands
  over the fixed list `Finset.univ.toList` of all `4ⁿ` Pauli
  strings. Each factor — including the identity string's global phase — is a genuine register
  `Evolution` (that is exactly why `pauliTrotterSummand` is a *total* function of `g`), so the
  product is a well-defined circuit.
-/

open scoped InnerProductSpace

open Matrix

noncomputable section

namespace AxQM

variable {n : ℕ}

/-- **One full Trotter step** `∏_g exp(-i h_g g t)` (Nielsen & Chuang, Problem 4.3(6)), as one
`Evolution (qudit (2ⁿ))`: the ordered product over *all* `4ⁿ` Pauli strings `g : Fin n → Fin 4`
(the fixed list `Finset.univ.toList`) of the total per-string summands `pauliTrotterSummand n g
(h g) t`. Each summand — including the identity string `g = I^{⊗n}` (whose summand is a global
phase) — is a genuine register `Evolution`, so the product is a well-defined circuit.

For `t = Δ = 1/k` and `h g = h_g` this is N&C's `∏_g exp(-i h_g g Δ)`, the single Trotter step
whose `k`-fold power approximates `U`.
-/
def pauliTrotterStep (n : ℕ) (h : (Fin n → Fin 4) → ℝ) (t : ℝ) : Evolution (qudit (2 ^ n)) :=
  (Finset.univ.toList.map fun g => pauliTrotterSummand n g (h g) t).prod

end AxQM
