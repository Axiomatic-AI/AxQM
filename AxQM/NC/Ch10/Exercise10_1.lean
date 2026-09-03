/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ThreeQubitBitFlipCode

/-!
# Nielsen & Chuang, Exercise 10.1 — the three-qubit bit-flip encoding circuit

*(N&C p. 428.)*

Verify the encoding circuit of Fig 10.2 encodes a|0>+b|1> as a|000>+b|111>.

* `bitFlipEncode_evolvePure_qubitSuperposition` — the exercise: the encoder takes `a|0⟩ + b|1⟩`
  (with the two `|0⟩` ancillae) to `a|000⟩ + b|111⟩`, i.e. `bitFlipEncode.evolvePure
  (qubitSuperposition a b h ⊗ |0⟩ ⊗ |0⟩) = bitFlipCodeword a b h`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 10.1.** The encoding circuit of Figure 10.2 takes the general
single-qubit state `a|0⟩ + b|1⟩` (fed in with two `|0⟩` ancillae) to the three-qubit codeword
`a|000⟩ + b|111⟩`: `bitFlipEncode.evolvePure (qubitSuperposition a b h ⊗ |0⟩ ⊗ |0⟩) =
bitFlipCodeword a b h`.
-/
theorem bitFlipEncode_evolvePure_qubitSuperposition (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    bitFlipEncode.evolvePure (qubitSuperposition a b h ⊗ qubitBasis 0 ⊗ qubitBasis 0)
      = bitFlipCodeword a b h := sorry

end AxQM
