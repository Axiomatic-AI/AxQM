/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.FourGateReversibleWire
import AxQM.Basic.API.Evolution
import AxQM.Concrete.PauliNormalizerGenerators
import AxQM.Concrete.PermutationGate
import AxQM.Concrete.MultiControlledNot

/-!
# The Figure-4.19 parity `CNOT` fan as a register `Evolution`

Nielsen & Chuang **Problem 4.3(3)** — "implement `exp(-i h_g g Δ)` using `O(n)` one- and two-qubit
gates" — computes the parity `⊕_{i∈S} xᵢ` of a Pauli string's support onto a single *collector*
wire `c` with a fan of `CNOT`s (Figure 4.19): a reverse `CNOT` fan with controls `t ∈ ts` and
target `c`.
To *count* it with the elementary-gate budget `CircuitBudget`
(which addresses `Evolution`s on the qubit control tower), the fan must first be a register
`Evolution`.

## Main declarations
* `cnotWireEvolution n a b` — a single `CNOT` with control `a` and target `b`, placed on the
  `2ⁿ`-level register as an `Evolution (qudit (2ⁿ))`: it is `mcNotWireEvolution n {a} b` (the
  one-control multiply-controlled `NOT`) when `a ≠ b`, and the identity when `a = b` (a
  self-targeting `CNOT` is undefined; the identity fallback makes the gate a total function of the
  two wires, exactly as `Concrete.cnotStep` returns the empty circuit for `t = c`).

* `cnotFanIntoEvolution n c ts` — the reverse `CNOT` fan into the collector `c`, as one
  `Evolution (qudit (2ⁿ))`: the ordered product `∏_{t ∈ ts} cnotWireEvolution n t c` of the per-
  control `CNOT`s (a `List.prod` over the control list `ts`). For a collector `c ∉ ts` its
  `ts.length` factors are genuine `CNOT`s (each `≤ 2`-control), the `O(n)` two-qubit gates of
  Figure 4.19.
-/

open scoped InnerProductSpace Matrix

namespace AxQM

noncomputable section

/-- **A single `CNOT` on register wires, control `a`, target `b`.** Placed on the `2ⁿ`-level
register `qudit (2ⁿ)` as an `Evolution`: the one-control multiply-controlled `NOT`
`mcNotWireEvolution n {a} b` when `a ≠ b` (`b ∉ {a}`), and the identity `1` when `a = b`. The
identity fallback makes `cnotWireEvolution` a total function of `(a, b)` — a self-targeting `CNOT`
being undefined — mirroring `Concrete.cnotStep`, whose circuit is empty for `t = c`. It is the
single-`CNOT` factor the parity fan `cnotFanIntoEvolution` is built from. -/
def cnotWireEvolution (n : ℕ) (a b : Fin n) : Evolution (qudit (2 ^ n)) :=
  if h : b = a then 1 else mcNotWireEvolution n {a} b (Finset.notMem_singleton.mpr h)

/-- **The reverse `CNOT` fan into a collector wire `c`, as a register `Evolution`.** The ordered
product `∏_{t ∈ ts} cnotWireEvolution n t c` of the per-control `CNOT`s `CNOT_{t→c}` (control
`t ∈ ts`, target the collector `c`), placed on the `2ⁿ`-level register `qudit (2ⁿ)`.
Reading the product right-to-left is Figure 4.19's parity
accumulation, each `CNOT_{t→c}` adding `x_t` into the collector's bit. For a collector `c ∉ ts` all
`ts.length` factors are genuine `≤ 2`-control `CNOT`s, so the fan costs `ts.length` two-qubit gates
— the `O(n)` two-qubit gates of Problem 4.3(3). -/
def cnotFanIntoEvolution (n : ℕ) (c : Fin n) (ts : List (Fin n)) : Evolution (qudit (2 ^ n)) :=
  (ts.map fun t => cnotWireEvolution n t c).prod

end

end AxQM
