/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledReduction
import AxQM.Concrete.MultiControlledNot

/-!
# The computational basis of the control tower (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for an `O(n²)`-gate no-work-qubit circuit of Toffoli,
`CNOT` and single-qubit gates implementing the `n`-controlled `NOT` `Cⁿ(X)`. Every such gate is a
permutation of the computational basis, described classically by the multiply-controlled `NOT`
`Concrete.mcNot S t` on bit-strings `Fin m → Fin 2`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

open AxQM.Concrete

/-- **The `(n+1)`-qubit computational basis** `towerKet n b` of the control register
`qtower n qubit = qubitⁿ ⊗ qubit`, indexed by a bit-string `b : Fin (n+1) → Fin 2` with wire `0` the
outermost control and wire `n` the target: the product state `|b 0⟩ ⊗ |b 1⟩ ⊗ … ⊗ |b n⟩`. -/
def towerKet : (n : ℕ) → (Fin (n + 1) → Fin 2) → PureState (qtower n qubit)
  | 0, b => qubitBasis (b 0)
  | n + 1, b => (qubitBasis (b 0)).tmul (towerKet n (fun i => b i.succ))

end AxQM
