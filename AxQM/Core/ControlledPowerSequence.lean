/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledReduction

/-!
# The phase-estimation controlled-`U` sequence — first stage of Figure 5.2 (Nielsen & Chuang §5.2)

The building blocks behind the first stage of the phase-estimation circuit
(N&C Figure 5.2): a `t`-qubit control register wrapping a target `S`, and, for each control wire, a
controlled power of `U` acting on `S`. On a computational-basis control `|j⟩ = |j₁…j_t⟩` the wire
`jₛ` applies `U^{jₛ·2^{t-s}}`, so the whole sequence applies `Uʲ`.

## Main declarations
* `qtowerKet t b u` — the input state `|b₀…b_{t-1}⟩ ⊗ |u⟩` on the register `qtower t S` (`t` control
  qubits wrapping the target `S`), for a bit-string `b : Fin t → Fin 2` (`b 0` the outermost /
  most-significant wire) and an **arbitrary** target pure state `u : PureState S`.
* `seqCtrlPow U t` — the sequence of controlled-`U` operations of Figure 5.2, as an `Evolution` on
  `qtower t S`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The phase-estimation input state** `|b₀ … b_{t-1}⟩ ⊗ |u⟩` on `qtower t S` (`t` control qubits
wrapping the target `S`): the control register in the computational-basis state indexed by the
bit-string `b : Fin t → Fin 2` (`b 0` the outermost / most-significant wire), tensored with an
arbitrary target pure state `u`. -/
def qtowerKet : (t : ℕ) → (Fin t → Fin 2) → PureState S → PureState (qtower t S)
  | 0, _, u => u
  | (t + 1), b, u => (qubitBasis (b 0)) ⊗ qtowerKet t (Fin.tail b) u

/-- **The sequence of controlled-`U` operations of Figure 5.2**, as an `Evolution` on the register
`qtower t S`. Recursion on the number of controls. -/
def seqCtrlPow (U : Evolution S) : (t : ℕ) → Evolution (qtower t S)
  | 0 => Evolution.id
  | (t + 1) => (controlledUnitary (unCtrl t (U ^ 2 ^ t))).comp ((seqCtrlPow U t).onRight qubit)

end AxQM
