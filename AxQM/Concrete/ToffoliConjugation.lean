/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Sqrt2IntegerMatrix
import AxQM.Concrete.Pauli
import AxQM.Concrete.PauliOuterProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Concrete: conjugation of the Pauli matrices by the Toffoli gate (N&C eqs 10.93–10.95)

The Toffoli half of Nielsen & Chuang **Exercise 10.41**, namely equations (10.93)–(10.95)
describing the action by conjugation of the **Toffoli gate** `U` — controls on qubits `1, 2`, target
qubit `3` — on the three-qubit Pauli operators. Below, `Zₖ` and `Xₖ` are the Pauli operators on
qubit `k` of the three-qubit register.

## Main results
* `toffoli_conj_pauliZ1, toffoli_conj_pauliZ2, toffoli_conj_pauliX3` — the three fixed generators
  (`U Z₁ U† = Z₁`, `U Z₂ U† = Z₂`, `U X₃ U† = X₃`).
* `toffoli_conj_pauliX1, toffoli_conj_pauliX2, toffoli_conj_pauliZ3` — the three non-Pauli images
  `U X₁ U† = X₁ (I + Z₂ + X₃ − Z₂X₃)/2`, `U X₂ U† = X₂ (I + Z₁ + X₃ − Z₁X₃)/2`,
  `U Z₃ U† = Z₃ (I + Z₁ + Z₂ − Z₁Z₂)/2`, witnessing `U ∉ N(G₃)`.
-/

open Matrix Complex
open scoped Kronecker

namespace AxQM.Concrete.ToffoliConj

/-- The big-endian re-indexing `((q₁, q₂), q₃) ↦ 4q₁ + 2q₂ + q₃` of a three-qubit tensor index to
`Fin 8`, i.e. the computational-basis order `|000⟩, …, |111⟩`. -/
def triQubitEquiv : (Fin 2 × Fin 2) × Fin 2 ≃ Fin 8 :=
  (finProdFinEquiv.prodCongr (Equiv.refl (Fin 2))).trans finProdFinEquiv

/-- Flatten a `((Fin 2 × Fin 2) × Fin 2)`-indexed matrix (a three-factor tensor/Kronecker product,
associated as `(A ⊗ₖ B) ⊗ₖ C`) to its `8 × 8` representation, ordering the tensor index by the
big-endian equiv `triQubitEquiv`. -/
def flattenTriQubit (M : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ) :
    Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.reindex triQubitEquiv triQubitEquiv M

/-- `X₁ = X ⊗ I ⊗ I`. -/
def pauliX1 : Matrix (Fin 8) (Fin 8) ℂ := flattenTriQubit (pauliX ⊗ₖ pauliI ⊗ₖ pauliI)
/-- `Z₁ = Z ⊗ I ⊗ I`. -/
def pauliZ1 : Matrix (Fin 8) (Fin 8) ℂ := flattenTriQubit (pauliZ ⊗ₖ pauliI ⊗ₖ pauliI)
/-- `X₂ = I ⊗ X ⊗ I`. -/
def pauliX2 : Matrix (Fin 8) (Fin 8) ℂ := flattenTriQubit (pauliI ⊗ₖ pauliX ⊗ₖ pauliI)
/-- `Z₂ = I ⊗ Z ⊗ I`. -/
def pauliZ2 : Matrix (Fin 8) (Fin 8) ℂ := flattenTriQubit (pauliI ⊗ₖ pauliZ ⊗ₖ pauliI)
/-- `X₃ = I ⊗ I ⊗ X`. -/
def pauliX3 : Matrix (Fin 8) (Fin 8) ℂ := flattenTriQubit (pauliI ⊗ₖ pauliI ⊗ₖ pauliX)
/-- `Z₃ = I ⊗ I ⊗ Z`. -/
def pauliZ3 : Matrix (Fin 8) (Fin 8) ℂ := flattenTriQubit (pauliI ⊗ₖ pauliI ⊗ₖ pauliZ)

attribute [local simp] flattenTriQubit triQubitEquiv finProdFinEquiv Fin.divNat Fin.modNat
  pauliX pauliY pauliZ pauliI

/-- `U Z₁ U† = Z₁` (Nielsen & Chuang, eq. 10.93, first identity). -/
theorem toffoli_conj_pauliZ1 : toffoliMatrix * pauliZ1 * toffoliMatrixᴴ = pauliZ1 := sorry

/-- `U Z₂ U† = Z₂` (Nielsen & Chuang, eq. 10.94, first identity). -/
theorem toffoli_conj_pauliZ2 : toffoliMatrix * pauliZ2 * toffoliMatrixᴴ = pauliZ2 := sorry

/-- `U X₃ U† = X₃` (Nielsen & Chuang, eq. 10.95, first identity). -/
theorem toffoli_conj_pauliX3 : toffoliMatrix * pauliX3 * toffoliMatrixᴴ = pauliX3 := sorry

set_option maxHeartbeats 1000000 in
-- Multiplying out three explicit `8 × 8` matrices entrywise exceeds the default heartbeat budget.
theorem toffoli_conj_pauliX1 :
    toffoliMatrix * pauliX1 * toffoliMatrixᴴ
      = pauliX1 * ((2 : ℂ)⁻¹ • (1 + pauliZ2 + pauliX3 - pauliZ2 * pauliX3)) := sorry

set_option maxHeartbeats 1000000 in
-- Multiplying out three explicit `8 × 8` matrices entrywise exceeds the default heartbeat budget.
theorem toffoli_conj_pauliX2 :
    toffoliMatrix * pauliX2 * toffoliMatrixᴴ
      = pauliX2 * ((2 : ℂ)⁻¹ • (1 + pauliZ1 + pauliX3 - pauliZ1 * pauliX3)) := sorry

set_option maxHeartbeats 1000000 in
-- Multiplying out three explicit `8 × 8` matrices entrywise exceeds the default heartbeat budget.
theorem toffoli_conj_pauliZ3 :
    toffoliMatrix * pauliZ3 * toffoliMatrixᴴ
      = pauliZ3 * ((2 : ℂ)⁻¹ • (1 + pauliZ1 + pauliZ2 - pauliZ1 * pauliZ2)) := sorry

end AxQM.Concrete.ToffoliConj
