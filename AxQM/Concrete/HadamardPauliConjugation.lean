/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Hadamard
import AxQM.Concrete.Pauli

/-!
# Concrete: conjugating the Pauli matrices by the Hadamard gate (Nielsen & Chuang, Exercise 4.13)

Nielsen & Chuang, Exercise 4.13 (*Circuit identities*, p. 177) asks to prove the three
Hadamard-conjugation identities (eq. 4.18).

## Main declarations
* `hadamardC_mul_pauliX_mul_hadamardC` — `H X H = Z`.
* `hadamardC_mul_pauliY_mul_hadamardC` — `H Y H = -Y`.
* `hadamardC_mul_pauliZ_mul_hadamardC` — `H Z H = X`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **Nielsen & Chuang, Exercise 4.13 (eq. 4.18)**: conjugating `X` by the Hadamard gate gives `Z`,
`H X H = Z`. The Hadamard reflection exchanges the `x̂` and `ẑ` Bloch axes. -/
theorem hadamardC_mul_pauliX_mul_hadamardC : hadamardC * pauliX * hadamardC = pauliZ := sorry

/-- **Nielsen & Chuang, Exercise 4.13 (eq. 4.18)**: conjugating `Y` by the Hadamard gate negates it,
`H Y H = -Y`. The Hadamard reflection flips the `ŷ` Bloch axis. -/
theorem hadamardC_mul_pauliY_mul_hadamardC : hadamardC * pauliY * hadamardC = -pauliY := sorry

/-- **Nielsen & Chuang, Exercise 4.13 (eq. 4.18)**: conjugating `Z` by the Hadamard gate gives `X`,
`H Z H = X`. The Hadamard reflection exchanges the `ẑ` and `x̂` Bloch axes. -/
theorem hadamardC_mul_pauliZ_mul_hadamardC : hadamardC * pauliZ * hadamardC = pauliX := sorry

end AxQM.Concrete
