/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ConditionalPhaseShift
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.ProjectorHamiltonian
import AxQM.Basic.API.RelativePhaseToffoli
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The marking oracle and the projector-Hamiltonian simulation circuit (N&C Exercise 6.7, Fig 6.4)

Nielsen & Chuang, §6.2 ("Quantum search as a quantum simulation", p. 258) simulates the search
Hamiltonian `H = |x⟩⟨x| + |ψ⟩⟨ψ|` (eq. 6.18) by alternately simulating its two projector summands.
**Figure 6.4** is the circuit for the first summand: it implements `exp(-i|x⟩⟨x|Δt)` using **two
oracle calls** flanking a single-qubit phase gate, a textbook *compute–phase–uncompute* circuit.
This file builds that circuit and proves its correctness at the underlying operator level.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Unitarity of the marking oracle** `|x⟩⟨x| ⊗ X + (I − |x⟩⟨x|) ⊗ I`. The operator is a
self-adjoint involution. -/
theorem markingOracle_op_mem_unitary (x : PureState S) :
    (TensorProduct.mapL (rankOne ℂ x.vec x.vec) pauliXGate.op
      + TensorProduct.mapL (1 - rankOne ℂ x.vec x.vec) 1)
      ∈ unitary (S.space ⊗[ℂ] qubit.space →L[ℂ] S.space ⊗[ℂ] qubit.space) := by
  set P : S.space →L[ℂ] S.space := rankOne ℂ x.vec x.vec with hP
  set X : qubit.space →L[ℂ] qubit.space := pauliXGate.op with hX
  have hPP : P * P = P := InnerProductSpace.isIdempotentElem_rankOne_self x.normalized
  have hXX : X * X = 1 := by
    have := congrArg Evolution.op pauliXGate_comp_pauliXGate
    rwa [Evolution.comp_op, Evolution.id_op, ← ContinuousLinearMap.mul_def] at this
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by rw [sub_mul, one_mul, hPQ, sub_zero]
  have hPQsum : P + (1 - P) = 1 := by abel
  have hadjP : adjoint P = P := by rw [hP, InnerProductSpace.adjoint_rankOne]
  have hadjX : adjoint X = X := by
    have := congrArg Evolution.op
      (Evolution.adjoint_eq_self_of_comp_self pauliXGate pauliXGate_comp_pauliXGate)
    rwa [Evolution.adjoint_op] at this
  have hadj1' : adjoint (1 : qubit.space →L[ℂ] qubit.space) = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  have hadjQ : adjoint (1 - P) = 1 - P := by
    rw [map_sub, hadjP]; rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  have hsa : star (TensorProduct.mapL P X + TensorProduct.mapL (1 - P) 1)
      = TensorProduct.mapL P X + TensorProduct.mapL (1 - P) 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint, map_add, TensorProduct.mapL_adjoint,
      TensorProduct.mapL_adjoint, hadjP, hadjX, hadjQ, hadj1']
  have hinv : (TensorProduct.mapL P X + TensorProduct.mapL (1 - P) 1)
      * (TensorProduct.mapL P X + TensorProduct.mapL (1 - P) 1) = 1 := by
    rw [mul_add, add_mul, add_mul, ← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul,
      ← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul, hPP, hXX, hPQ, hQP, hQQ]
    simp only [TensorProduct.mapL_zero_left, add_zero, zero_add, mul_one, one_mul]
    rw [← TensorProduct.mapL_add_left, hPQsum, TensorProduct.mapL_one]
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩ <;> rw [hsa] <;> exact hinv

/-- **The marking oracle** `O = |x⟩⟨x| ⊗ X + (I − |x⟩⟨x|) ⊗ I` for a marked pure state `x`, as an
`Evolution` on the query register `S` tensored with a response qubit. It flips the response
qubit exactly when the query is in the marked state `x`. This is N&C's search oracle for a
single marked item (§6.2, the `f(q) = [q = x]` bit-flip oracle), extended linearly to an
arbitrary marked pure state. Unitarity is `markingOracle_op_mem_unitary` (a self-adjoint
involution). -/
def markingOracle (x : PureState S) : Evolution (S ⊗ qubit) where
  op := TensorProduct.mapL (rankOne ℂ x.vec x.vec) pauliXGate.op
      + TensorProduct.mapL (1 - rankOne ℂ x.vec x.vec) 1
  unitary := markingOracle_op_mem_unitary x

/-- **The Figure 6.4 simulation circuit** `O · (I ⊗ P(-Δt)) · O` for `exp(-i|x⟩⟨x|Δt)`: the
marking oracle `O = markingOracle x`, then the response-qubit phase gate `P(-Δt) =
phaseShiftGate (-Δt) = diag(1, e^{-iΔt})`, then the marking oracle again — the
compute–phase–uncompute circuit of N&C §6.2 using **two** oracle calls. -/
def hamSimCircuit (x : PureState S) (Δt : ℝ) : Evolution (S ⊗ qubit) :=
  (markingOracle x).comp (((phaseShiftGate (-Δt)).onRight S).comp (markingOracle x))

end AxQM
