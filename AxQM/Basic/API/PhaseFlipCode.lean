/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.QubitThree
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.QuantumErrorCorrection

/-!
# AxQM.Basic.API — the three-qubit phase-flip code and its QEC conditions

Nielsen & Chuang's **Exercise 10.8** (p. 441) concerns the three-qubit *phase-flip code*, with
logical states `|+++⟩` and `|−−−⟩`.

## Contents

* `pmQubit` — the single-qubit `±` orthonormal frame `0 ↦ |+⟩`, `1 ↦ |−⟩`.
* `pmThreeVec` — the three-qubit `±`-basis vector `|σ₁σ₂σ₃⟩`.
* `phaseFlipErrorGate` / `phaseFlipErrorOp` — the error gates `{I, Z₁, Z₂, Z₃}` as evolutions and as
  operators.
* `phaseFlipCodeword` — the logical codewords `|+++⟩`, `|−−−⟩`; `phaseFlipCodeProj` — the code
  projector `P = |+++⟩⟨+++| + |−−−⟩⟨−−−|`.
* `phaseFlipCode_satisfiesQECConditions` — **Exercise 10.8**: `SatisfiesQECConditions
  phaseFlipCodeProj phaseFlipErrorOp` (the conditions hold with the identity Hermitian matrix).
-/

open scoped InnerProductSpace TensorProduct Matrix
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The single-qubit `±` orthonormal frame** `{|+⟩, |−⟩}`, as a family indexed by `Fin 2` (`0 ↦
|+⟩`, `1 ↦ |−⟩`). -/
def pmQubit : Fin 2 → qubit.space := ![qubitPlus.vec, qubitMinus.vec]

/-- **The three-qubit `±`-basis vector** `|σ₁σ₂σ₃⟩ = |σ₁⟩ ⊗ (|σ₂⟩ ⊗ |σ₃⟩)` (each `σᵢ` selecting
`|+⟩` or `|−⟩`) of the register `qubit ⊗ (qubit ⊗ qubit)`. The eight such vectors form an
orthonormal basis; the two codewords `|+++⟩`, `|−−−⟩` are the `(0,0,0)` and `(1,1,1)` members. -/
def pmThreeVec (s : Fin 2 × Fin 2 × Fin 2) : (qubit ⊗ (qubit ⊗ qubit)).space :=
  pmQubit s.1 ⊗ₜ[ℂ] (pmQubit s.2.1 ⊗ₜ[ℂ] pmQubit s.2.2)

/-- **The error gates** `{I, Z₁, Z₂, Z₃}` on the three-qubit register, as evolutions.
-/
def phaseFlipErrorGate : Fin 4 → Evolution (qubit ⊗ (qubit ⊗ qubit))
  | 0 => Evolution.id
  | 1 => pauliZGate.onLeft (qubit ⊗ qubit)
  | 2 => (pauliZGate.onLeft qubit).onRight qubit
  | 3 => (pauliZGate.onRight qubit).onRight qubit

/-- **The error operators** `{I, Z₁, Z₂, Z₃}` as operators on the register state space — the
operation elements of the noise the phase-flip code protects against (the `.op` of
`phaseFlipErrorGate`). -/
def phaseFlipErrorOp (i : Fin 4) :
    (qubit ⊗ (qubit ⊗ qubit)).space →L[ℂ] (qubit ⊗ (qubit ⊗ qubit)).space :=
  (phaseFlipErrorGate i).op

/-- **The logical codewords of the three-qubit phase-flip code:** `|0_L⟩ = |+++⟩` (`a = 0`) and
`|1_L⟩ = |−−−⟩` (`a = 1`). -/
def phaseFlipCodeword (a : Fin 2) : (qubit ⊗ (qubit ⊗ qubit)).space := pmThreeVec (a, a, a)

/-- **The code projector** `P = |+++⟩⟨+++| + |−−−⟩⟨−−−|` onto the phase-flip code space. -/
def phaseFlipCodeProj : (qubit ⊗ (qubit ⊗ qubit)).space →L[ℂ] (qubit ⊗ (qubit ⊗ qubit)).space :=
  ∑ a, InnerProductSpace.rankOne ℂ (phaseFlipCodeword a) (phaseFlipCodeword a)

/-- **Nielsen & Chuang, Exercise 10.8.** The three-qubit phase-flip code
(`|0_L⟩ = |+++⟩`, `|1_L⟩ = |−−−⟩`) satisfies the quantum error-correction conditions
for the error set `{I, Z₁, Z₂, Z₃}`: the code projector `phaseFlipCodeProj` and error operators
`phaseFlipErrorOp` satisfy `SatisfiesQECConditions` with the **identity** Hermitian coefficient
matrix `α = 1` (`P Eᵢ† Eⱼ P = δᵢⱼ P`). Hence `{I, Z₁, Z₂, Z₃}` is a correctable set. -/
theorem phaseFlipCode_satisfiesQECConditions :
    SatisfiesQECConditions phaseFlipCodeProj phaseFlipErrorOp := sorry

end AxQM
