/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorCodeBitFlip
import AxQM.Basic.API.ShorStabilizer
import AxQM.Basic.API.CatVerification
import AxQM.Basic.API.RelativePhaseToffoli
import AxQM.Basic.API.ControlledControlledUnitary
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Nielsen & Chuang, Exercise 10.69 (a single fault gives at most one bit-flip error)

*(N&C p. 491.)*

Show a single failure in ancilla prep/verification causes at most one X or Y error in the ancilla
output.

* `catVerifyGate`
* `catVerifyFaultCircuit`
* `catAncilla_single_fault_at_most_one_error`
-/

noncomputable section

namespace AxQM

/-- **The verification gadget for one parity check `ZᵢZⱼ`** (Figure 10.28's `Z₂Z₃` step), on
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)` with qubits `0, 1` the two ancilla qubits under test and
qubit `2` the fresh extra (syndrome) qubit: two `CNOT`s from the ancilla qubits (controls) into the
extra qubit (shared target), `catVerifyGate = CNOT₁₂ ∘ CNOT₀₂`. On the `|0⟩`-initialised extra
qubit it deposits the parity `q₀ + q₁` there; reading the extra qubit is the verification
measurement. -/
def catVerifyGate : Evolution bitFlipReg :=
  (cnotGate.onRight qubit).comp cnotFirstThirdGate

/-! ### A single fault at *any* gadget time-slice

Exercise 10.69 asks for a single failure anywhere in the verification, and N&C (p. 490)
call out the fault *between* the two `CNOT`s as a physically distinct position. A single fault
strikes the gadget `catVerifyGate = CNOT₁₂ ∘ CNOT₀₂` at one of three time-slices — before `CNOT₀₂`
(`input`), between the two `CNOT`s (`between`), or after `CNOT₁₂` (`output`) — and propagates only
through the gates that *follow* it. Its bit-flip part is an arbitrary residue `e : Fin 3 → Fin 2`
subject to the **single-fault** constraint `(e 0 : ℕ) + (e 1 : ℕ) ≤ 1`, that it touch at most one
*ancilla* qubit. -/

/-- **The three time-slices at which a single fault can strike the `ZᵢZⱼ` verification gadget**
`catVerifyGate = CNOT₁₂ ∘ CNOT₀₂`: before `CNOT₀₂`, between the two `CNOT`s, or after `CNOT₁₂`.
Together they exhaust the positions at which a single failure can strike the verification
(N&C §10.6.3, p. 490). -/
inductive CatVerifyFaultSlice
  /-- A fault before `CNOT₀₂` — the gadget input. -/
  | input
  /-- A fault between `CNOT₀₂` and `CNOT₁₂` (the position N&C single out on p. 490). -/
  | between
  /-- A fault after `CNOT₁₂` — the gadget output. -/
  | output

/-- **The verification gadget with a bit-flip fault `X^{e}` injected at time-slice `s`.** The
remaining gates act on the fault: `input` places it before the whole gadget
(`catVerifyGate ∘ X^{e}`), `between` between the two `CNOT`s (`CNOT₁₂ ∘ X^{e} ∘ CNOT₀₂`), and
`output` after the gadget (`X^{e} ∘ catVerifyGate`). -/
def catVerifyFaultCircuit : CatVerifyFaultSlice → (Fin 3 → Fin 2) → Evolution bitFlipReg
  | .input, e => catVerifyGate.comp (blockBitFlipPattern e)
  | .between, e => ((cnotGate.onRight qubit).comp (blockBitFlipPattern e)).comp cnotFirstThirdGate
  | .output, e => (blockBitFlipPattern e).comp catVerifyGate

/-- **Nielsen & Chuang, Exercise 10.69.** A single failure anywhere in the preparation or the
verification of the cat ancilla leads to at most one `X` or `Y` error in the ancilla output. The
fault's location is encoded as a `Sum`: a **preparation** fault (`Sum.inl p`) fans out to an
arbitrary bit-flip residue `p` on the `n`-qubit cat ancilla `bitReg ι`, and is either rejected by a
parity check `ZᵢZⱼ` or leaves the accepted ancilla with a residue of weight `≤ 1`; a
**verification** fault (`Sum.inr (s, e)`) is a bit-flip residue `e` injected at any time-slice `s`
of the `ZᵢZⱼ` gadget, subject to the single-fault constraint `e₀ + e₁ ≤ 1`, and leaves the ancilla
output with a residue of weight `≤ 1`. -/
theorem catAncilla_single_fault_at_most_one_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (fault : (ι → ZMod 2) ⊕ CatVerifyFaultSlice × (Fin 3 → Fin 2)) :
    fault.elim
      (fun p => (∃ i j, (zPairObservable i j).HasEigenstate (-1)
                    ((bitString p).evolvePure (catState ι)))
                  ∨ (∃ r : ι → ZMod 2, (∑ i, (r i).val) ≤ 1 ∧
                      (bitString p).evolvePure (catState ι)
                        = (bitString r).evolvePure (catState ι)))
      (fun se => (se.2 0 : ℕ) + (se.2 1 : ℕ) ≤ 1 →
                  ∃ r : Fin 3 → Fin 2, (r 0 : ℕ) + (r 1 : ℕ) ≤ 1 ∧
                    catVerifyFaultCircuit se.1 se.2
                      = (blockBitFlipPattern r).comp catVerifyGate) := sorry

end AxQM
