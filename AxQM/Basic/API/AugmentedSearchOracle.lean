/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.RelativePhaseToffoli
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.Qudit
import AxQM.Basic.API.DeutschAlgorithm

/-!
# The augmented search oracle `O'` over the whole search index

Nielsen & Chuang, §6.1.4 (p. 255): to search a space in which *more than half* the items may be
solutions, one **doubles** the search space by adjoining a single extra qubit `|q⟩`, and builds an
**augmented oracle** `O'` that marks an item `(x, q)` iff `x` is a solution *and* the extra bit is
`q = 0`. Exercise 6.5 asks to show `O'` can be constructed from **one call** to the original oracle
`O` together with **elementary quantum gates**, using the extra qubit `|q⟩`.

## Main declarations
* `IsSearchBitFlipOracle f O` — the abstract one-call oracle: `O|x⟩|a⟩|b⟩ = |x⟩|a⟩|b ⊕ f(x)⟩`.
* `augmentedSearchOracle O` — the seven-factor circuit built from **one** `O` and the elementary
  gates `X_r`, `CNOT_{q→r}`, `H_r`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {N : ℕ} {f : Fin N → Fin 2}
  {O : Evolution ((qudit N).compose (qubit.compose qubit))}

/-- **The abstract one-call bit-flip oracle** for `f : Fin N → Fin 2` on the augmented register
`qudit N ⊗ (qubit ⊗ qubit)` (index `|x⟩`, extra qubit `|a⟩`, response `|b⟩`): the reversible XOR
oracle `O|x⟩|a⟩|b⟩ = |x⟩|a⟩|b ⊕ f(x)⟩`, adding `f(x)` into the response and leaving both the
index `x` and the extra qubit `a` alone. -/
def IsSearchBitFlipOracle (f : Fin N → Fin 2)
    (O : Evolution ((qudit N).compose (qubit.compose qubit))) : Prop :=
  ∀ (x : Fin N) (a b : Fin 2),
    O.evolvePure ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis b)))
      = (quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis (b + f x)))

/-- **The elementary gate `X_r`** on the augmented register: `pauliX` on the response qubit `r`,
identity on the index `x` and the extra qubit `q`, i.e. `1_x ⊗ (1_q ⊗ X_r)`. -/
def xFlipResponse : Evolution ((qudit N).compose (qubit.compose qubit)) :=
  (pauliXGate.onRight qubit).onRight (qudit N)

/-- **The elementary gate `CNOT_{q→r}`** on the augmented register: the controlled-`NOT` with the
extra qubit `q` as control and the response `r` as target, identity on the index `x`, i.e.
`1_x ⊗ CNOT_{q→r}`. -/
def cnotExtraResponse : Evolution ((qudit N).compose (qubit.compose qubit)) :=
  cnotGate.onRight (qudit N)

/-- **The elementary gate `H_r`** on the augmented register: the Hadamard on the response qubit `r`,
identity on the index `x` and the extra qubit `q`, i.e. `1_x ⊗ (1_q ⊗ H_r)`. -/
def hadResponse : Evolution ((qudit N).compose (qubit.compose qubit)) :=
  (hadamardGate.onRight qubit).onRight (qudit N)

/-- **The augmented search oracle `O'` from one oracle call.** In time order `X_r`, `CNOT_{q→r}`,
`H_r`, the single oracle call `O`, `H_r`, `CNOT_{q→r}`, `X_r` — a palindrome of the elementary
gates `X_r`, `CNOT_{q→r}`, `H_r` around a **single** call to the oracle `O`. -/
def augmentedSearchOracle
    (O : Evolution ((qudit N).compose (qubit.compose qubit))) :
    Evolution ((qudit N).compose (qubit.compose qubit)) :=
  (xFlipResponse.comp cnotExtraResponse).comp
    ((hadResponse.comp (O.comp hadResponse)).comp
      (cnotExtraResponse.comp xFlipResponse))

end AxQM
