/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorCodePhaseFlip

/-!
# Nielsen & Chuang, Exercise 10.6 — recovery from a phase flip via `Z₁Z₂Z₃`

*(N&C p. 433.)*

Recovery from a phase flip on any of first three Shor-code qubits via applying Z1Z2Z3.

* `blockPhaseFlip_recovery` — the exercise: applying `Z₁Z₂Z₃` after a phase flip on any of the three
  qubits returns the block to its original encoded state, `Z₁Z₂Z₃ · Zᵢ · |catBlockState σ⟩ =
  |catBlockState σ⟩`.
-/

noncomputable section

namespace AxQM

/-- **Exercise 10.6 — recovery from a phase flip via `Z₁Z₂Z₃`.** Applying the recovery gate
`Z₁Z₂Z₃` (`blockZGate`) *after* a phase flip on *any* of the block's three qubits
(`blockPhaseFlip i`, `i : Fin 3`) returns the block to its original encoded state `catBlockState σ`.
The single operator `Z₁Z₂Z₃` corrects the phase-flip error irrespective of which of the three
qubits it occurred on — the content of the exercise. -/
theorem blockPhaseFlip_recovery (i : Fin 3) (σ : Fin 2) :
    blockZGate.evolvePure ((blockPhaseFlip i).evolvePure (catBlockState σ)) = catBlockState σ :=
      sorry

end AxQM
