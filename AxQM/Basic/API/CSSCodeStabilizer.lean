/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CSSCode

/-!
# Pauli strings stabilize CSS coset states

This file records the general **stabilizer** facts for the CSS coset states: for a binary
code `C₂ = LinearCode (ZMod 2) ι` and a codeword register `bitReg ι`, when do the local
Pauli strings `X^v` (`bitString v`) and `Z^u` (`phaseString u`) fix the standard coset
state `|x + C₂⟩` (`cssStdState C₂ x`)?
-/

namespace AxQM

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)]

/-- **Action of `Z^u` on a standard CSS state when `u ⊥ C₂`** (underlying operator form): if `u` is
orthogonal
to every codeword of `C₂`, the diagonal string `Z^u` multiplies `|x + C₂⟩` by the *uniform* sign
`(-1)^{u·x}`. Each ket `|x + y⟩` picks up `(-1)^{u·(x+y)} = (-1)^{u·x + u·y} = (-1)^{u·x}` because
`u·y = 0`, so the sign is constant across the superposition and factors out. -/
theorem phaseString_op_cssStdState_vec_smul {u : ι → ZMod 2} (x : ι → ZMod 2)
    (huy : ∀ y ∈ C₂, u ⬝ᵥ y = 0) :
    (phaseString u).op (cssStdState C₂ x).vec
      = (-1 : ℂ) ^ (u ⬝ᵥ x).val • (cssStdState C₂ x).vec := by
  rw [cssStdState_vec, Evolution.op_smul_sum, smul_comm]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [phaseString_op_regBasis, dotProduct_add, huy _ y.2, add_zero]

/-- **`Z^u` acts as the sign `(-1)^{u·x}` on `|x + C₂⟩` when `u ⊥ C₂`.** If `u` is orthogonal to
every codeword of `C₂`, then `Z^u` is an eigenvalue-`(-1)^{u·x}` eigenstate on the standard coset
state. The sign distinguishes the two logical cosets — the mechanism by which `Z̄ = Z^{𝟙}` acts
as logical `Z` on a CSS code. -/
theorem phaseString_hasEigenstate_cssStdState {u : ι → ZMod 2} (x : ι → ZMod 2)
    (huy : ∀ y ∈ C₂, u ⬝ᵥ y = 0) :
    (phaseString u).HasEigenstate ((-1 : ℂ) ^ (u ⬝ᵥ x).val) (cssStdState C₂ x) :=
  phaseString_op_cssStdState_vec_smul C₂ x huy

end AxQM
