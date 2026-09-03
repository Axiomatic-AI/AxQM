/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorPauliError

/-!
# AxQM.Basic.API — the Shor-code error family and off-diagonal error-vector overlaps

Infrastructure for Nielsen & Chuang's **Exercise 10.10**: the verification of the
quantum error-correction conditions for the nine-qubit Shor code against the error
set `{I} ∪ {X_j, Y_j, Z_j : j = 1..9}` (the identity and every single-qubit Pauli). This file
collects the **error family** the verification rests on.

## Contents

* `ShorErrorIndex` — the index set `Option (Fin 3 × Fin 3 × Fin 3)` of the 28 errors: `none = I`,
  `some (t, block, pos)` the Pauli of type `t` (`0 = X`, `1 = Y`, `2 = Z`) on qubit `(block, pos)`.
* `shorErrorFamily` — the error operators `Eᵢ` (`none ↦ 1`, `some ↦ shorPauliError`).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The index set of the 28 Shor-code errors** of Exercise 10.10. The 27 Pauli errors plus the
single identity make up the error set `{I} ∪ {X_j, Y_j, Z_j : j = 1..9}`. -/
abbrev ShorErrorIndex : Type := Option (Fin 3 × Fin 3 × Fin 3)

/-- **The Shor-code error operators** `Eᵢ` indexed by `ShorErrorIndex`: the identity `I = 1` for
`none`, and the single-qubit Pauli error `shorPauliError t block pos` for `some (t, block, pos)`.
These are the operation elements the quantum error-correction conditions (Theorem 10.1,
Exercise 10.10) are checked against. -/
def shorErrorFamily : ShorErrorIndex → shorReg.space →L[ℂ] shorReg.space
  | none => 1
  | some (t, block, pos) => shorPauliError t block pos

end AxQM
