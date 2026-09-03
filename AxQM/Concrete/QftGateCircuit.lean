/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledSingleQubit
import AxQM.Concrete.SingleQubitWire
import AxQM.Concrete.Hadamard
import AxQM.Concrete.PermutationGate
import AxQM.Concrete.QftGateCount
import Mathlib.Algebra.BigOperators.Fin

/-!
# Concrete: the gate-level Figure 5.1 quantum-Fourier-transform circuit

Nielsen & Chuang, §5.1, p. 219, Figure 5.1, give the **efficient circuit for the quantum Fourier
transform** on `n` qubits: process the wires in turn, applying to wire `t` one Hadamard followed by
a cascade of *controlled-`Rₖ`* phase rotations from the later wires, and finish with swap gates that
reverse the wire order.

## Main declarations
* `qftTargetControls n t` — the later wires `t+1, …, n-1` that control target `t`;
  `qftBitReversal n` — the wire-reversing permutation of the swap layer.

**Endianness — why the swap layer comes first.** Under the little-endian encoding
`finFunctionFinEquiv` (`k = ∑ₗ kₗ 2ˡ`, wire `0` the *least* significant), the blocks process wire
`0` first with its controls drawn from the *higher* wires, so wire `0` plays the most-significant
role and the block cascade builds the QFT's phases in reverse-bit order. Placing the wire-reversal
**before** the blocks, rather than after as in a big-endian drawing of Figure 5.1, is what makes
the resulting matrix the little-endian one. The swap layer's *position* is immaterial to
Exercise 5.6: the perturbable controlled-`Rₖ` gates and their count are unchanged; only the
parameter-free swap moves to the input end.
-/

namespace AxQM.Concrete

open Matrix

/-- **The Hadamard gate on wire `t`** of the `n`-qubit register — the parameter-free gate that
opens each block of Figure 5.1 (`singleQubitOnWire` with the complex Hadamard `hadamardC`). -/
noncomputable def qftHadamardGate (n : ℕ) (t : Fin n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  singleQubitOnWire finFunctionFinEquiv t hadamardC

/-- **The control wires of target `t`:** the later wires `t+1, …, n-1`, obtained by dropping the
first `t+1` wires of `List.finRange n`. -/
def qftTargetControls (n : ℕ) (t : Fin n) : List (Fin n) :=
  (List.finRange n).drop ((t : ℕ) + 1)

/-- **The wire-reversal permutation** realised by the swap layer at the end of Figure 5.1: it
reverses the order of the `n` wires (`f ↦ f ∘ Fin.rev`). -/
def qftBitReversal (n : ℕ) : Equiv.Perm (Fin n → Fin 2) :=
  Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 2))

end AxQM.Concrete
