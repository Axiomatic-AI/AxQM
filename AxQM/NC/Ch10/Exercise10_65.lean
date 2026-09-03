/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.OneBitTeleportation
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.RelativePhaseToffoli

/-!
# Nielsen & Chuang, Exercise 10.65 (measured swap into `|0⟩`)

*(N&C p. 487.)*

Show two given CNOT+measurement+classically-controlled circuits accomplish qubit swap into |0>.

* `swapViaCnots` — the reference two-`CNOT` swap `reversedCNOT · CNOT`.
* `swapViaCnots_evolvePure_ketZero` — its action `|ψ⟩ ⊗ |0⟩ ↦ |0⟩ ⊗ |ψ⟩`.
* `measuredSwapCircuit1_corrected`, `measuredSwapCircuit2_corrected` — the task is done: after the
  circuit, the control measurement (outcome `m`), and the classically-controlled `Z^m` (circuit 1) /
  `X^m` (circuit 2) correction on the target, the state is `|m⟩ ⊗ |ψ⟩` — the unknown `|ψ⟩` moved
  onto the second qubit, for both outcomes.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The reference two-`CNOT` swap -/

/-- **The reference two-`CNOT` swap** of N&C Exercise 10.65: `reversedCNOT · CNOT`, a `CNOT`
(control = qubit 1) then the reversed `CNOT` (control = qubit 2).  Applied to `|ψ⟩ ⊗ |0⟩` it swaps
unknown `|ψ⟩` onto the second qubit — the "task" the measured circuits must reproduce. -/
def swapViaCnots : Evolution (qubit ⊗ qubit) :=
  reversedCnotGate.comp cnotGate

/-- **The reference two-`CNOT` swap accomplishes the task:** `reversedCNOT · CNOT · (|ψ⟩ ⊗ |0⟩) =
|0⟩ ⊗ |ψ⟩`. -/
theorem swapViaCnots_evolvePure_ketZero (ψ : PureState qubit) :
    swapViaCnots.evolvePure (ψ.tmul (qubitBasis 0)) = (qubitBasis 0).tmul ψ := sorry

/-! ### The two measured-swap circuits accomplish the same task -/

/-- **Circuit 1 accomplishes the task** (N&C Exercise 10.65, first circuit): after the control
measurement with outcome `m` and the classically-controlled `Z` correction, the state is
`|m⟩ ⊗ |ψ⟩`. -/
theorem measuredSwapCircuit1_corrected (ψ : PureState qubit) (m : Fin 2)
    (hp : (controlMeasurement qubit).bornProb
        (measuredSwapCircuit1.evolvePure (ψ.tmul (qubitBasis 0))).toState m ≠ 0) :
    (classicalControl pauliZGate m).evolve
        ((controlMeasurement qubit).postMeasurement
          (measuredSwapCircuit1.evolvePure (ψ.tmul (qubitBasis 0))).toState m hp)
      = ((qubitBasis m).tmul ψ).toState := sorry

/-- **Circuit 2 accomplishes the task** (N&C Exercise 10.65, second circuit): after the control
measurement with outcome `m` and the classically-controlled `X` correction, the state is
`|m⟩ ⊗ |ψ⟩`. -/
theorem measuredSwapCircuit2_corrected (ψ : PureState qubit) (m : Fin 2)
    (hp : (controlMeasurement qubit).bornProb
        (measuredSwapCircuit2.evolvePure (ψ.tmul (qubitBasis 0))).toState m ≠ 0) :
    (classicalControl pauliXGate m).evolve
        ((controlMeasurement qubit).postMeasurement
          (measuredSwapCircuit2.evolvePure (ψ.tmul (qubitBasis 0))).toState m hp)
      = ((qubitBasis m).tmul ψ).toState := sorry

end AxQM
