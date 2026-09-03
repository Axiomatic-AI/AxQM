/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorCodeBlock
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.Teleportation
import AxQM.Basic.Composite
import AxQM.Basic.API.RelativePhaseToffoli

/-!
# AxQM.Basic.API — block-level bit-flip gates and their action on the cat state

Infrastructure for the **bit-flip (`X`) errors** on one three-qubit cat block
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)` carrying the cat vector
`catBlockVec σ = |000⟩ + (−1)^σ |111⟩`
(Nielsen & Chuang, Exercise 10.69, fault-tolerant cat-state measurement, §10.6.3).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The single-qubit bit-flip selected by a bit** `a : Fin 2`: `X⁰ = 1` (no flip) for `a = 0`,
`X¹ = X` (flip) for `a = 1`. The per-qubit ingredient of a bit-flip *pattern*. -/
def pauliXSelect : Fin 2 → Evolution qubit
  | 0 => Evolution.id
  | 1 => pauliXGate

/-- **A bit-flip pattern gate on a block:** `X^{p₀} ⊗ X^{p₁} ⊗ X^{p₂}` on
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`, flipping exactly the qubits `i` with `p i = 1`. It models an
arbitrary bit-flip error on the block — the shape of the residue any single fault leaves after
propagating to the ancilla output. -/
def blockBitFlipPattern (p : Fin 3 → Fin 2) : Evolution bitFlipReg :=
  pauliXSelect (p 0) ⊗ (pauliXSelect (p 1) ⊗ pauliXSelect (p 2))

end AxQM
