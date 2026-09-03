/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliEigen
import AxQM.Basic.API.Observable
import AxQM.Basic.API.PauliMeasurement
import AxQM.Basic.API.CascadedMeasurement
import AxQM.Basic.API.QubitThree
import AxQM.Concrete.TensorScalar

/-!
# AxQM.Basic.API — the three-qubit bit-flip syndrome measurement

Infrastructure for Nielsen & Chuang §10.1.1 / Exercise 10.3: the syndrome
measurement of the three-qubit bit-flip code, described **two ways** — as a cascade of two
`±1` observable measurements, and as a single four-outcome projective measurement — together
with the operator identity that makes the two descriptions coincide.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- The **three-qubit register** `qubit ⊗ (qubit ⊗ qubit)`, the physical system of the three-qubit
bit-flip code. -/
abbrev bitFlipReg : QSystem := qubit ⊗ (qubit ⊗ qubit)

/-- **`Z₁Z₂ = Z ⊗ Z ⊗ I`**, the first syndrome observable (N&C eq. 10.12): compares qubits 1 and 2.
-/
def zzIObservable : Observable bitFlipReg :=
  pauliZObservable ⊗ (pauliZObservable ⊗ Observable.id qubit)

/-- **`Z₂Z₃ = I ⊗ Z ⊗ Z`**, the second syndrome observable: compares qubits 2 and 3. -/
def izzObservable : Observable bitFlipReg :=
  Observable.id qubit ⊗ (pauliZObservable ⊗ pauliZObservable)

/-- **`Z₁Z₂` acts diagonally:** `Z₁Z₂ |b₁b₂b₃⟩ = (−1)^{b₁+b₂} |b₁b₂b₃⟩` (only the first two qubits'
`Z`s contribute; the third factor is the identity). -/
theorem zzI_op_ket (b : Fin 2 × Fin 2 × Fin 2) :
    zzIObservable.op (qubitThreeBasis b).vec
      = ((-1 : ℂ) ^ (b.1 : ℕ) * (-1 : ℂ) ^ (b.2.1 : ℕ)) • (qubitThreeBasis b).vec := by
  simp only [qubitThreeBasis, PureState.tmul_vec, zzIObservable, Observable.tmul_op_tmul,
    Observable.id_op, ContinuousLinearMap.one_apply, pauliZObservable_op_apply_qubitBasis]
  exact Concrete.smul_tmul_smul_tmul_left _ _ _ _ _

/-- **`Z₂Z₃` acts diagonally:** `Z₂Z₃ |b₁b₂b₃⟩ = (−1)^{b₂+b₃} |b₁b₂b₃⟩`. -/
theorem izz_op_ket (b : Fin 2 × Fin 2 × Fin 2) :
    izzObservable.op (qubitThreeBasis b).vec
      = ((-1 : ℂ) ^ (b.2.1 : ℕ) * (-1 : ℂ) ^ (b.2.2 : ℕ)) • (qubitThreeBasis b).vec := by
  simp only [qubitThreeBasis, PureState.tmul_vec, izzObservable, Observable.tmul_op_tmul,
    Observable.id_op, ContinuousLinearMap.one_apply, pauliZObservable_op_apply_qubitBasis]
  exact Concrete.tmul_smul_tmul_smul_right _ _ _ _ _

/-- **`Z₁Z₂` is a self-adjoint involution:** `(Z₁Z₂)² = I`. -/
theorem zzI_involution : zzIObservable.op * zzIObservable.op = 1 := by
  apply qubitThree_op_ext
  intro b
  rw [ContinuousLinearMap.mul_apply, zzI_op_ket, map_smul, zzI_op_ket, smul_smul,
    ContinuousLinearMap.one_apply]
  fin_cases b <;> simp

/-- **`Z₂Z₃` is a self-adjoint involution:** `(Z₂Z₃)² = I`. -/
theorem izz_involution : izzObservable.op * izzObservable.op = 1 := by
  apply qubitThree_op_ext
  intro b
  rw [ContinuousLinearMap.mul_apply, izz_op_ket, map_smul, izz_op_ket, smul_smul,
    ContinuousLinearMap.one_apply]
  fin_cases b <;> simp

/-- **Measuring `Z₁Z₂`**: the two-outcome projective measurement of the observable `Z₁Z₂`
(outcome `0 ↔ +1`, `1 ↔ −1`). -/
def bitFlipZ12Measurement : Measurement (Fin 2) bitFlipReg :=
  zzIObservable.signMeasurement zzI_involution

/-- **Measuring `Z₂Z₃`**: the two-outcome projective measurement of the observable `Z₂Z₃`. -/
def bitFlipZ23Measurement : Measurement (Fin 2) bitFlipReg :=
  izzObservable.signMeasurement izz_involution

/-- The two computational basis strings supporting each of N&C's four syndrome projectors:
`0 ↦ {000, 111}` (no error), `1 ↦ {100, 011}` (qubit 1), `2 ↦ {010, 101}` (qubit 2),
`3 ↦ {001, 110}` (qubit 3). -/
def bitFlipSyndromeStr : Fin 4 → (Fin 2 × Fin 2 × Fin 2) × (Fin 2 × Fin 2 × Fin 2) :=
  ![((0, 0, 0), (1, 1, 1)), ((1, 0, 0), (0, 1, 1)), ((0, 1, 0), (1, 0, 1)), ((0, 0, 1), (1, 1, 0))]

/-- **The four bit-flip syndrome projectors** of N&C eqns (10.5)–(10.8): `Pᵢ` is the sum of the two
rank-one projectors onto the computational basis states of `bitFlipSyndromeStr i`, e.g.
`P₀ = |000⟩⟨000| + |111⟩⟨111|`. -/
def bitFlipSyndromeProj (i : Fin 4) : bitFlipReg.space →L[ℂ] bitFlipReg.space :=
  rankOne ℂ (qubitThreeBasis (bitFlipSyndromeStr i).1).vec
      (qubitThreeBasis (bitFlipSyndromeStr i).1).vec
    + rankOne ℂ (qubitThreeBasis (bitFlipSyndromeStr i).2).vec
        (qubitThreeBasis (bitFlipSyndromeStr i).2).vec

/-- **The outcome relabeling** of Exercise 10.3: the pair of `±1` measurement outcomes `(s₁, s₂)`
maps to the syndrome label `i ∈ {0,1,2,3}` by N&C's dictionary `(+,+) ↦ 0` (no error),
`(−,+) ↦ 1` (bit flip on qubit 1), `(−,−) ↦ 2` (qubit 2), `(+,−) ↦ 3` (qubit 3). -/
def bitFlipRelabel : Fin 2 × Fin 2 ≃ Fin 4 where
  toFun := fun s => ![![0, 3], ![1, 2]] s.1 s.2
  invFun := fun i => ![(0, 0), (1, 0), (1, 1), (0, 1)] i
  left_inv := by decide
  right_inv := by decide

/-- **The core operator identity of Exercise 10.3.** For every joint outcome `(s₁, s₂)`, the
measurement operator of the cascade "measure `Z₁Z₂` then `Z₂Z₃`" equals the bit-flip syndrome
projector `P_{bitFlipRelabel (s₁,s₂)}`. -/
theorem cascade_op_eq_syndromeProj (s : Fin 2 × Fin 2) :
    (bitFlipZ12Measurement.cascade bitFlipZ23Measurement).op s
      = bitFlipSyndromeProj (bitFlipRelabel s) := by
  apply qubitThree_op_ext
  intro b
  obtain ⟨s1, s2⟩ := s
  rw [Measurement.cascade_op, ContinuousLinearMap.comp_apply]
  simp only [bitFlipZ12Measurement, bitFlipZ23Measurement]
  fin_cases s1 <;> fin_cases s2 <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Observable.signMeasurement_op_zero,
      Observable.signMeasurement_op_one, Observable.projPlus_apply_smul _ (zzI_op_ket b),
      Observable.projMinus_apply_smul _ (zzI_op_ket b),
      Observable.projPlus_apply_smul _ (izz_op_ket b),
      Observable.projMinus_apply_smul _ (izz_op_ket b), map_smul, smul_smul, bitFlipRelabel,
      Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, bitFlipSyndromeProj,
      bitFlipSyndromeStr, ContinuousLinearMap.add_apply, qubitThreeBasis_rankOne_apply] <;>
    fin_cases b <;> norm_num

/-- **Measuring the four bit-flip syndrome projectors** as a single four-outcome projective
measurement (N&C eqns 10.5–10.8). -/
def bitFlipSyndromeMeasurement : Measurement (Fin 4) bitFlipReg where
  op := bitFlipSyndromeProj
  complete := by
    rw [← Equiv.sum_comp bitFlipRelabel (fun i => (adjoint (bitFlipSyndromeProj i)).comp
      (bitFlipSyndromeProj i))]
    simp only [← cascade_op_eq_syndromeProj]
    exact (bitFlipZ12Measurement.cascade bitFlipZ23Measurement).complete

end AxQM
