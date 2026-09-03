/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ThreeQubitBitFlipCode
import AxQM.Basic.API.QuditMeasurement
import AxQM.Basic.API.PeriodShift
import AxQM.Basic.API.ThreeQubitBitFlipRecovery
import AxQM.Basic.API.Fidelity
import AxQM.Basic.API.TraceDistance
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
import AxQM.Concrete.ClassicalTraceDistance

/-!
# Nielsen & Chuang, Exercise 10.4 — the eight-projector syndrome measurement of the bit-flip code

*(N&C p. 432.)*

Three qubit bit flip: eight computational-basis projectors; recovery works only for basis states;
min fidelity.

* `logicalZero`
* `logicalOne`
* `bitFlipError`
* `bitFlipError_diagnoses_syndrome`
* `bitFlipRecovery_apply_logicalZero`
* `bitFlipRecovery_apply_logicalOne`
* `bitFlipRecovery_apply_encoded_ne`
* `threeQubitBitFlip_minFidelity`
-/

open scoped InnerProductSpace
open AxQM.Concrete

noncomputable section

namespace AxQM

/-- The **logical zero** `|0_L⟩ = |000⟩` of the three qubit bit flip code, the computational-basis
state `|0⟩` of `qudit 8`. -/
def logicalZero : PureState (qudit 8) := quditBasis 0

/-- The **logical one** `|1_L⟩ = |111⟩` of the three qubit bit flip code, the computational-basis
state `|7⟩` of `qudit 8`. -/
def logicalOne : PureState (qudit 8) := quditBasis 7

/-- A **single-qubit bit-flip error** on the three-qubit register, indexed by the syndrome value `j
: Fin 4` it produces. -/
def bitFlipError (j : Fin 4) : Evolution (qudit 8) := quditPerm (xorPerm (errorMask j))

/-- **Part (1): the eight-projector measurement diagnoses the error syndrome.** Applying a
single-qubit bit-flip error `bitFlipError j` (`j : Fin 4`, `j = 0` = no error) to either logical
codeword `c ∈ {|000⟩, |111⟩}` and then measuring the eight computational-basis projectors is a
*deterministic* measurement: there is a unique outcome `y` that occurs with probability one, and
its majority-vote syndrome `syndrome y` equals `j`.
-/
theorem bitFlipError_diagnoses_syndrome (j : Fin 4) (c : Fin 8) (hc : c = 0 ∨ c = 7) :
    ∃ y : Fin 8, syndrome y = j ∧ ∀ x : Fin 8,
      (quditMeasurement 8).bornProb ((bitFlipError j).evolvePure (quditBasis c)).toState x
        = if x = y then 1 else 0 := sorry

/-- **Part (2): the recovery is faithful on the logical zero `|0_L⟩ = |000⟩`.** Applying the
eight-projector recovery `bitFlipRecovery` to the basis codeword `|0_L⟩` returns it unchanged:
measuring `|000⟩` is certain to give outcome `000`, whose syndrome is `0`, so the (trivial)
correction leaves it fixed. A computational basis state is recovered exactly. -/
theorem bitFlipRecovery_apply_logicalZero :
    bitFlipRecovery.apply logicalZero.toState = logicalZero.toState := sorry

/-- **Part (2): the recovery is faithful on the logical one `|1_L⟩ = |111⟩`.** As for `|0_L⟩`, the
basis codeword `|1_L⟩` is recovered exactly: measuring `|111⟩` gives outcome `111` with certainty,
syndrome `0`, and the correction leaves it fixed. -/
theorem bitFlipRecovery_apply_logicalOne :
    bitFlipRecovery.apply logicalOne.toState = logicalOne.toState := sorry

/-- **Part (2): the recovery destroys a genuine code superposition.** For an encoded logical qubit
`a|0_L⟩ + b|1_L⟩` with *both* amplitudes nonzero, the eight-projector recovery does **not**
return the input state: `bitFlipRecovery.apply ρ ≠ ρ`. -/
theorem bitFlipRecovery_apply_encoded_ne (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    bitFlipRecovery.apply (encodedCodeState a b h).toState ≠ (encodedCodeState a b h).toState :=
      sorry

/-- **Part (3): the minimum fidelity for the error-correction procedure is `1/√2`.** Over all
encoded logical qubits `ψ_L = a|0_L⟩ + b|1_L⟩` (`‖a‖² + ‖b‖² = 1`), the least fidelity the
eight-projector error-correction procedure achieves is `1/√2 = √2/2`, attained at the equal
superposition `‖a‖² = ‖b‖² = 1/2`.

Two facts make `1/√2` the exact worst-case fidelity of the full procedure, independent of `p`:
(i) at the equal superposition the recovered diagonal state `‖a‖²|000⟩⟨000| + ‖b‖²|111⟩⟨111|`
has fidelity `1/√2` with the input; and (ii) every *correctable* single-qubit bit-flip carries
`ψ_L` to another basis-pair superposition whose recovery is the same diagonal state (the
majority vote fixes the error), so no correctable error changes the fidelity. Thus the noiseless
recovery here already realises the worst case, and the answer is the `p`-independent `1/√2`.
-/
theorem threeQubitBitFlip_minFidelity :
    IsLeast {F : ℝ | ∃ (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1),
        (encodedCodeState a b h).toState.fidelity
          (bitFlipRecovery.apply (encodedCodeState a b h).toState) = F} (Real.sqrt 2 / 2) := sorry

end AxQM
