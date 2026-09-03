/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliStringExpCircuit
import AxQM.Basic.API.NMRControlledZ
import AxQM.Concrete.PauliStringLocality

/-!
# The total per-string Trotter summand `exp(-i h_g g Δ)` over all `4ⁿ` strings (N&C Problem 4.3(6))

Nielsen & Chuang, Problem 4.3(6) assembles the universal approximation `U ≈ [∏_g exp(-i h_g g Δ)]ᵏ`
as the `k`-fold power (part (5)) of one Trotter step, itself the ordered product over **all** `4ⁿ`
Pauli strings `g : Fin n → Fin 4` of the summands `exp(-i h_g g Δ)`. For that product to be a
well-defined `Evolution`-valued function of `g`, each summand — including the one for the **identity
string** `g = I^{⊗n}` — must be a single register `Evolution`. This file supplies exactly that total
function.

## Main declarations
* `pauliTrotterSummand n g coeff t` — the Trotter summand `exp(-i · coeff · t · g)` of the
  Pauli-string Hamiltonian `coeff · g`, as one `Evolution (qudit (2ⁿ))`, defined by cases on the
  **support** `Concrete.pauliStringSupport g = {k | g k ≠ 0}`:
  * **nonempty support** (a genuine Pauli rotation): the Figure-4.19 compute–rotate–uncompute
    cascade `pauliStringExpCircuit n g c ts (2 · coeff · t)`, with collector `c = min'` of the
    support and remaining support wires `ts = (support.erase c).toList` (so the string's support is
    exactly `insert c ts`);
  * **empty support** (the identity string `g = I^{⊗n}`, whose summand `exp(-i coeff t · I)` is a
    *global phase*, not a Pauli rotation — the part-(3) circuit needs a nonempty support/collector,
    so it does not cover this case): the global-phase gate `globalPhaseGate (-(coeff · t))`.
-/

open scoped InnerProductSpace

open Matrix

noncomputable section

namespace AxQM

variable {n : ℕ}

/-- **The total per-string Trotter summand** `exp(-i · coeff · t · g)` (Nielsen & Chuang,
Problem 4.3(6)), as one `Evolution (qudit (2ⁿ))`, defined for *every* Pauli string
`g : Fin n → Fin 4` by cases on its support `Concrete.pauliStringSupport g`:

* **nonempty support** — a genuine Pauli rotation: the Figure-4.19 cascade
  `pauliStringExpCircuit n g c ts (2 · coeff · t)` with collector `c` the least support wire and
  `ts` the remaining support wires, so `g`'s support is exactly `insert c ts`;
* **empty support** — the identity string `g = I^{⊗n}`, whose summand `exp(-i coeff t · I)` is the
  global phase `e^{-i coeff t} · I`: the gate `globalPhaseGate (-(coeff · t))`.

For `coeff = h_g`, `t = Δ` this is N&C's `exp(-i h_g g Δ)`, the factor of the Trotter product
`∏_g exp(-i h_g g Δ)`. -/
def pauliTrotterSummand (n : ℕ) (g : Fin n → Fin 4) (coeff t : ℝ) :
    Evolution (qudit (2 ^ n)) :=
  if hne : (Concrete.pauliStringSupport g).Nonempty then
    pauliStringExpCircuit n g ((Concrete.pauliStringSupport g).min' hne)
      (((Concrete.pauliStringSupport g).erase
        ((Concrete.pauliStringSupport g).min' hne)).toList) (2 * coeff * t)
  else
    globalPhaseGate (-(coeff * t))

end AxQM
