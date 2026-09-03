/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.Reflection
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.ControlBranchExt
import AxQM.Basic.API.BellBasis

/-!
# AxQM.Basic.API — the two-qubit conditional phase shift `2|00⟩⟨00| − I`

Nielsen & Chuang's **conditional phase shift** on two qubits (the `n = 2` case of the Grover phase
shift, N&C eq. 6.5 / Exercise 6.1): the gate `2|00⟩⟨00| − I` that fixes `|00⟩` and negates every
other computational-basis state.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **A unitary involution is self-adjoint:** if `U · U = 1` then `U† = U`. -/
theorem Evolution.adjoint_eq_self_of_comp_self {S : QSystem} (U : Evolution S)
    (h : U.comp U = Evolution.id) : U.adjoint = U :=
  calc U.adjoint
      = U.adjoint.comp Evolution.id := (Evolution.comp_id _).symm
    _ = U.adjoint.comp (U.comp U) := by rw [h]
    _ = (U.adjoint.comp U).comp U := (Evolution.comp_assoc _ _ _).symm
    _ = Evolution.id.comp U := by rw [Evolution.adjoint_comp_self']
    _ = U := Evolution.id_comp _

/-- The two-qubit computational-basis product state `|00⟩ = |0⟩ ⊗ |0⟩`. -/
def ketZeroZero : PureState (qubit ⊗ qubit) := qubitBasis 0 ⊗ qubitBasis 0

/-- **The conditional phase shift** `2|00⟩⟨00| − I` on two qubits (Nielsen & Chuang, Box 6.1 /
Exercise 6.1 at `n = 2`): the closed-system `Evolution` that fixes `|00⟩` and phase-flips every
other computational-basis state. -/
def conditionalPhaseShiftZeroZero : Evolution (qubit ⊗ qubit) where
  op := (2 : ℂ) • rankOne ℂ ketZeroZero.vec ketZeroZero.vec - 1
  unitary := by
    have hself : inner ℂ ketZeroZero.vec ketZeroZero.vec = (1 : ℂ) :=
      inner_self_eq_one_of_norm_eq_one ketZeroZero.normalized
    set P : (qubit ⊗ qubit).space →L[ℂ] (qubit ⊗ qubit).space :=
      rankOne ℂ ketZeroZero.vec ketZeroZero.vec with hPdef
    have hPP : P * P = P := by
      rw [hPdef, ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hself, one_smul]
    have hPsa : star P = P := by
      rw [hPdef, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]
    have hRsa : star ((2 : ℂ) • P - 1) = (2 : ℂ) • P - 1 := by
      rw [star_sub, star_smul, hPsa, star_one, star_ofNat]
    have hRR : ((2 : ℂ) • P - 1) * ((2 : ℂ) • P - 1) = 1 := by
      simp only [mul_sub, sub_mul, one_mul, mul_one, smul_mul_smul_comm, hPP]
      module
    rw [Unitary.mem_iff, hRsa]
    exact ⟨hRR, hRR⟩

end AxQM
