/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EntropyExampleStates
import AxQM.NC.Ch2.Exercise2_72
import AxQM.NC.Ch11.Theorem11_8

/-!
# Nielsen & Chuang, Exercise 11.11 — example calculations of von Neumann entropy

*(N&C p. 511.)*

Calculate von Neumann entropy S(rho) for three specific 2x2 density matrices.

* `vonNeumannEntropy_entropyExampleZeroState`, `vonNeumannEntropy_entropyExamplePlusState` —
  `S(ρ) = 0` for (11.41) and (11.42): both have `‖r⃗‖ = 1`, hence are pure.
* `vonNeumannEntropy_entropyExampleMixedState` — `S(ρ) = H((3+√5)/6, (3−√5)/6)` for (11.43): its
  eigenvalues are `(1 ± √5/3)/2 = (3 ± √5)/6`, and the entropy is the binary Shannon entropy of that
  spectrum.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **N&C (11.41): `S(|0⟩⟨0|) = 0`.** The state `½(I + Z)` (`= !![1,0;0,0]`) has Bloch vector of
norm one, hence is pure, and a pure state has zero von Neumann entropy. -/
theorem vonNeumannEntropy_entropyExampleZeroState :
    entropyExampleZeroState.vonNeumannEntropy = 0 := sorry

/-- **N&C (11.42): `S(|+⟩⟨+|) = 0`.** The state `½(I + X)` (`= ½!![1,1;1,1]`) has Bloch vector of
norm one, hence is pure, and a pure state has zero von Neumann entropy. -/
theorem vonNeumannEntropy_entropyExamplePlusState :
    entropyExamplePlusState.vonNeumannEntropy = 0 := sorry

/-- **N&C (11.43): `S(⅓ !![2,1;1,1]) = H((3+√5)/6, (3−√5)/6)`.** The mixed qubit state
(`= ⅓!![2,1;1,1]`) has Bloch vector `(2/3, 0, 1/3)` of norm `√5/3`, so its eigenvalues are
`(1 ± √5/3)/2 = (3 ± √5)/6`, and its entropy is the binary Shannon entropy of that spectrum. -/
theorem vonNeumannEntropy_entropyExampleMixedState :
    entropyExampleMixedState.vonNeumannEntropy =
      Real.entropy ![(3 + Real.sqrt 5) / 6, (3 - Real.sqrt 5) / 6] := sorry

end AxQM
