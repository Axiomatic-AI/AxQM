/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CatVerification
import AxQM.Concrete.SXCorrectionMatrix

/-!
# AxQM.Basic.API — the transversal `T` gate on the cat ancilla

Infrastructure for the **"slight modification"** of the fault-tolerant measurement
procedure that Nielsen & Chuang use for the observable `M = e^{-iπ/4}SX` (§10.6.3, p. 491,
Exercise 10.71). To perform the controlled-`M` of Figure 10.28 for this `M`, N&C apply transversal
controlled-`ZSX` (the Clifford part) *followed by seven `T` gates applied transversally to the
ancilla qubits* — supplying the non-Clifford scalar `e^{-iπ/4}` as a **controlled relative phase**
between the two branches of the cat ancilla.
-/

open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- **The transversal `T` gate `T^{⊗n}`** on the register `bitReg ι`. This is the π/8 gate applied
bitwise to every qubit — each `T = diag(1, T₁₁)` contributes a factor `T₁₁` for each set bit —
the seven-`T` phase gadget of Exercise 10.71's slight modification, at general qubit count. -/
def transversalTGate : Evolution (bitReg ι) where
  op := (regBasis ι).diagonalOperator fun w => (Concrete.tMatrix 1 1) ^ (∑ i, (w i).val)
  unitary := (regBasis ι).diagonalOperator_mem_unitary _ fun w => by
    rw [norm_pow, Concrete.norm_tMatrix_one_one, one_pow]

/-- **The seven ancilla `T` gates supply `M`'s scalar `e^{-iπ/4}`** (the Steane-code instance, `ι =
Fin 7`): `T^{⊗7}|cat⟩ = |0…0⟩ + e^{-iπ/4}|1…1⟩`. On the seven-qubit Steane cat ancilla the
transversal `T` gadget applies the relative phase `(T₁₁)^{7} = e^{-iπ/4}` — **exactly the scalar
of `M = e^{-iπ/4}SX`** — on the active `|1…1⟩` branch and nothing on the `|0…0⟩` branch. This is
the operator-level content of Exercise 10.71's slight modification: the non-Clifford phase of `M`
is applied to the *ancilla* as a controlled relative phase between the cat branches, not folded
into the per-qubit transversal correction. -/
theorem transversalTGate_op_catVec_seven :
    (transversalTGate (Fin 7)).op (catVec (Fin 7))
      = regBasis (Fin 7) 0
        + Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) • regBasis (Fin 7) 1 := sorry

end AxQM
