/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EigenspaceCollapse
import AxQM.Basic.API.BellState
import AxQM.Basic.API.RelativePhase

/-!
# AxQM.Basic.API — measuring one half of an EPR pair

Local measurements of the *first* qubit of the maximally entangled Bell state
`|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` (`bellPhiPlus`), in the `X` and in the `Z` basis (Nielsen & Chuang,
Exercise 12.37, §12.6.5, p. 598).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {A : Observable qubit} {ψp ψm : PureState qubit}

/-- **Measure the first qubit in the `X` basis.** The projective (sign) measurement of the
observable `X ⊗ I` on `qubit ⊗ qubit`: its `±1` eigenprojectors are `|±⟩⟨±| ⊗ I`, i.e. it projects
the first qubit onto the `X` eigenbasis `{|+⟩, |-⟩}` while leaving the second untouched. Outcome
`0 ↔ +1`, `1 ↔ −1`. -/
def eprMeasureFirstX : Measurement (Fin 2) (qubit ⊗ qubit) :=
  (pauliXObservable.tmul (Observable.id qubit)).signMeasurement
    (Observable.tmul_op_mul_self pauliXObservable_op_mul_self (by simp [Observable.id_op]))

/-- **Measure the first qubit in the `Z` basis.** The projective (sign) measurement of the
observable `Z ⊗ I` on `qubit ⊗ qubit`: its `±1` eigenprojectors are `|0⟩⟨0| ⊗ I`, `|1⟩⟨1| ⊗ I`, the
computational-basis measurement of the first qubit. Outcome `0 ↔ +1` (`|0⟩`), `1 ↔ −1` (`|1⟩`). -/
def eprMeasureFirstZ : Measurement (Fin 2) (qubit ⊗ qubit) :=
  (pauliZObservable.tmul (Observable.id qubit)).signMeasurement
    (Observable.tmul_op_mul_self pauliZObservable_op_mul_self (by simp [Observable.id_op]))

end AxQM
