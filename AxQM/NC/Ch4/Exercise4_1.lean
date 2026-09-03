/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BlochState
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.Eigenstate
import AxQM.Concrete.PauliEigenstateBloch

/-!
# Nielsen & Chuang, Exercise 4.1 — Bloch-sphere points of the Pauli eigenvectors

*(N&C p. 174.)*

Find Bloch-sphere points for the normalized eigenvectors of the Pauli matrices.

* `qubitPlus_blochVector`
* `qubitMinus_blochVector`
* `qubitPlusI_blochVector`
* `qubitMinusI_blochVector`
* `qubitKet0_blochVector`
* `qubitBasis_one_blochVector`
* `qubitPlus_hasEigenstate_pauliX`
* `qubitMinus_hasEigenstate_pauliX`
* `qubitPlusI_hasEigenstate_pauliY`
* `qubitMinusI_hasEigenstate_pauliY`
* `qubitKet0_hasEigenstate_pauliZ`
* `qubitBasis_one_hasEigenstate_pauliZ`
-/

noncomputable section

namespace AxQM

/-! ### The Bloch points — the answer to Exercise 4.1

Each eigenvector's density operator is `blochState axis = ½(I + axis·σ⃗)`, so its Bloch vector is
the coordinate axis. -/

/-- **The Bloch point of `|+⟩` is `+x̂ = (1, 0, 0)`.** -/
theorem qubitPlus_blochVector :
    qubitPlus.toState = blochState ![1, 0, 0]
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]) := sorry

/-- **The Bloch point of `|-⟩` is `-x̂ = (-1, 0, 0)`.** -/
theorem qubitMinus_blochVector :
    qubitMinus.toState = blochState ![-1, 0, 0]
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]) := sorry

/-- **The Bloch point of `|+i⟩` is `+ŷ = (0, 1, 0)`.** -/
theorem qubitPlusI_blochVector :
    qubitPlusI.toState = blochState ![0, 1, 0]
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]) := sorry

/-- **The Bloch point of `|-i⟩` is `-ŷ = (0, -1, 0)`.** -/
theorem qubitMinusI_blochVector :
    qubitMinusI.toState = blochState ![0, -1, 0]
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]) := sorry

/-- **The Bloch point of `|0⟩` is `+ẑ = (0, 0, 1)`.** -/
theorem qubitKet0_blochVector :
    qubitKet0.toState = blochState ![0, 0, 1]
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]) := sorry

/-- **The Bloch point of `|1⟩` is `-ẑ = (0, 0, -1)`.** -/
theorem qubitBasis_one_blochVector :
    (qubitBasis 1).toState = blochState ![0, 0, -1]
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]) := sorry

/-! ### The states are the ±1 eigenstates of the Pauli observables

The observable-level reading of "the eigenvectors of the Pauli matrices": each of the six
states is a `±1` eigenstate of the Pauli vector observable `n⃗·σ⃗` (`Observable.HasEigenstate`). -/

/-- **`|+⟩` is the `+1` eigenstate of `X`:** `X |+⟩ = |+⟩`. -/
theorem qubitPlus_hasEigenstate_pauliX : pauliXObservable.HasEigenstate 1 qubitPlus := sorry

/-- **`|-⟩` is the `-1` eigenstate of `X`:** `X |-⟩ = -|-⟩`. -/
theorem qubitMinus_hasEigenstate_pauliX : pauliXObservable.HasEigenstate (-1) qubitMinus := sorry

/-- **`|+i⟩` is the `+1` eigenstate of `Y`:** `Y |+i⟩ = |+i⟩`. -/
theorem qubitPlusI_hasEigenstate_pauliY : pauliYObservable.HasEigenstate 1 qubitPlusI := sorry

/-- **`|-i⟩` is the `-1` eigenstate of `Y`:** `Y |-i⟩ = -|-i⟩`. -/
theorem qubitMinusI_hasEigenstate_pauliY : pauliYObservable.HasEigenstate (-1) qubitMinusI := sorry

/-- **`|0⟩` is the `+1` eigenstate of `Z`:** `Z |0⟩ = |0⟩`. -/
theorem qubitKet0_hasEigenstate_pauliZ : pauliZObservable.HasEigenstate 1 qubitKet0 := sorry

/-- **`|1⟩` is the `-1` eigenstate of `Z`:** `Z |1⟩ = -|1⟩`. -/
theorem qubitBasis_one_hasEigenstate_pauliZ :
    pauliZObservable.HasEigenstate (-1) (qubitBasis 1) := sorry

end AxQM
