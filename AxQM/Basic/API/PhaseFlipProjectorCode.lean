/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PhaseFlipCode
import AxQM.Basic.API.Swap
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Basic.API — the phase-flip code protects against `{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}`

Nielsen & Chuang's **Exercise 10.9** (p. 441) asks: *again consider the three-qubit phase-flip code*
(`|0_L⟩ = |+++⟩`, `|1_L⟩ = |−−−⟩`); *let `Pᵢ` and `Qᵢ` be the projectors onto the `|0⟩` and `|1⟩`
states, respectively, of the `i`-th qubit; prove that the code protects against the error set*
`{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}`.

## Contents

* `qubitZeroProj` / `qubitOneProj` — the single-qubit computational-basis projectors `|0⟩⟨0|`,
  `|1⟩⟨1|`.
* `phaseFlipFullError` — the error set `{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}` as operators on the register
  `qubit ⊗ (qubit ⊗ qubit)`, each `Pᵢ`/`Qᵢ` the single-wire projector `qubitZeroProj`/`qubitOneProj`
  embedded via `TensorProduct.mapL`.
* `phaseFlipCode_satisfiesQECConditions_fullErrorSet` — **Exercise 10.9**:
  `SatisfiesQECConditions phaseFlipCodeProj phaseFlipFullError`.
-/

open scoped InnerProductSpace TensorProduct Matrix
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The single-qubit projector `|0⟩⟨0|`** onto the computational basis state `|0⟩`. -/
def qubitZeroProj : qubit.space →L[ℂ] qubit.space :=
  rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec

/-- **The single-qubit projector `|1⟩⟨1|`** onto the computational basis state `|1⟩`. -/
def qubitOneProj : qubit.space →L[ℂ] qubit.space :=
  rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec

/-- **The error set `{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}` of Exercise 10.9**, as operators on the
three-qubit phase-flip register `qubit ⊗ (qubit ⊗ qubit)`. -/
def phaseFlipFullError : Fin 7 → (qubit ⊗ (qubit ⊗ qubit)).space →L[ℂ]
    (qubit ⊗ (qubit ⊗ qubit)).space
  | 0 => 1
  | 1 => TensorProduct.mapL qubitZeroProj 1
  | 2 => TensorProduct.mapL qubitOneProj 1
  | 3 => TensorProduct.mapL 1 (TensorProduct.mapL qubitZeroProj 1)
  | 4 => TensorProduct.mapL 1 (TensorProduct.mapL qubitOneProj 1)
  | 5 => TensorProduct.mapL 1 (TensorProduct.mapL 1 qubitZeroProj)
  | 6 => TensorProduct.mapL 1 (TensorProduct.mapL 1 qubitOneProj)

/-- **Nielsen & Chuang, Exercise 10.9.** The three-qubit phase-flip code (`|0_L⟩ = |+++⟩`, `|1_L⟩ =
|−−−⟩`) protects against the error set `{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}`, where `Pᵢ`/`Qᵢ` are the
projectors onto `|0⟩`/`|1⟩` of qubit `i`: the code projector `phaseFlipCodeProj` and the
projector error operators `phaseFlipFullError` satisfy the quantum error-correction conditions.
-/
theorem phaseFlipCode_satisfiesQECConditions_fullErrorSet :
    SatisfiesQECConditions phaseFlipCodeProj phaseFlipFullError := sorry

end AxQM
