/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CSSCode
import AxQM.Basic.API.MeasureObservable

/-!
# AxQM.Basic.API — the `n`-qubit cat ancilla and its parity-check verification

Infrastructure for the **verification** stage of the fault-tolerant cat-state
measurement, stated at **general qubit count**. To
measure an encoded observable fault-tolerantly N&C prepare an ancilla in a *cat state*
`|0…0⟩ + |1…1⟩` and then **verify** it by measuring the two-qubit parities `ZᵢZⱼ`: a genuine cat has
even parity across every pair, so a `−1` outcome flags a bit-flip error and the ancilla is
discarded. N&C's Figure 10.28 draws the cat on three qubits "for simplicity"; the real construction
(the seven-qubit Steane code) needs more, and it is only for `n ≥ 5` that the verification does
strictly more than the cat's own `X^{⊗n}` symmetry. This file therefore works over an **arbitrary**
qubit index type `ι` — the `n`-qubit register `bitReg ι`, with its computational basis `regBasis`,
bit-flip strings `bitString` (`X^v`, `|w⟩ ↦ |w + v⟩`) and phase strings `phaseString`
(`Z^u`, `|w⟩ ↦ (−1)^{u·w} |w⟩`).
-/

open scoped Matrix
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- **The unnormalised `n`-qubit cat vector** `|0…0⟩ + |1…1⟩` on the register `bitReg ι`: the sum of
the all-zeros and all-ones computational-basis vectors. This is the ancilla N&C prepare (and then
verify) for a fault-tolerant measurement (§10.6.3); the `+`-signed cat, encoding `|+⟩` under the
repetition structure. -/
def catVec : (bitReg ι).space := regBasis ι 0 + regBasis ι 1

/-- **The cat vector has inner product `2` with itself:** `⟪catVec, catVec⟫ = 2`. -/
theorem catVec_inner [Nonempty ι] :
    (inner ℂ (catVec ι) (catVec ι) : ℂ) = 2 := by
  have hii := (orthonormal_iff_ite (𝕜 := ℂ)).1 (regBasis ι).orthonormal
  simp only [catVec, inner_add_left, inner_add_right, hii]
  norm_num

/-- **The cat vector is nonzero** (on a nonempty register). -/
theorem catVec_ne_zero [Nonempty ι] : catVec ι ≠ 0 := by
  intro h
  have hi := catVec_inner (ι := ι)
  rw [h, inner_zero_right] at hi
  exact (by norm_num : (2 : ℂ) ≠ 0) hi.symm

variable (ι) in
/-- **The normalised `n`-qubit cat ancilla** `catState ι = |cat⟩/√2 = (|0…0⟩ + |1…1⟩)/√2`, a
`PureState` of `bitReg ι`. -/
def catState [Nonempty ι] : PureState (bitReg ι) :=
  PureState.normalize (catVec ι) catVec_ne_zero

/-- **The phase string `Z^u` is self-adjoint.** This is what makes `Z^u` a genuine `±1`
observable. -/
theorem phaseString_op_isSelfAdjoint (u : ι → ZMod 2) : IsSelfAdjoint (phaseString u).op := by
  rw [phaseString_op, isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint,
    (regBasis ι).diagonalOperator_adjoint]
  congr 1
  funext w
  simp [star_pow]

/-- **The two-qubit parity observable `ZᵢZⱼ`** on `bitReg ι`, the phase string `Z^{eᵢ + eⱼ}` viewed
as a `±1` observable (`Evolution.toObservable`). Its `+1`/`−1` outcome measures the *parity* of
qubits `i` and `j`: even (accept) or odd (reject). This
is the verification check of the cat ancilla (N&C §10.6.3). -/
def zPairObservable (i j : ι) : Observable (bitReg ι) :=
  (phaseString (Pi.single i 1 + Pi.single j 1)).toObservable (phaseString_op_isSelfAdjoint _)

end AxQM
