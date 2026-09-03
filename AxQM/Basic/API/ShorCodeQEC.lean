/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorErrorInnerProduct
import AxQM.Basic.API.QuantumErrorCorrection

/-!
# AxQM.Basic.API — the Shor code satisfies the QEC conditions (Exercise 10.10)

The assembly step of Nielsen & Chuang's **Exercise 10.10** (p. 441): the nine-qubit Shor code
`{|0_L⟩, |1_L⟩}` satisfies the quantum error-correction conditions (Theorem 10.1, Eq. (10.16)) for
the error set `{I} ∪ {X_j, Y_j, Z_j : j = 1..9}` — the identity together with every single-qubit
Pauli.

## Contents

* `shorCode_satisfiesQECConditions` — **Exercise 10.10**: `SatisfiesQECConditions shorCodeProj
  shorErrorFamily`, the Shor code satisfies the quantum error-correction conditions.
-/

open scoped InnerProductSpace TensorProduct Matrix
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 10.10.** The nine-qubit Shor code (logical codewords
`shorCodeword 0 = |0_L⟩`, `shorCodeword 1 = |1_L⟩`) satisfies the quantum error-correction
conditions for the error set `{I} ∪ {X_j, Y_j, Z_j : j = 1..9}`
(`shorErrorFamily`): the code projector `shorCodeProj` and error operators `shorErrorFamily` satisfy
`SatisfiesQECConditions`, i.e. `P Eᵢ† Eⱼ P = αᵢⱼ P` for some Hermitian `α`. Hence
`{I} ∪ {X_j, Y_j, Z_j}` is a correctable set for the Shor code — every single-qubit error is
correctable.

The matrix `α` is *not* diagonal: the Shor code is a **degenerate** code (distinct Paulis in the
same cat block act identically on the codewords up to phase), so this is genuinely N&C's "some
Hermitian `α`" condition, not the sharper orthonormal-image condition (`α = 1`) of the bit-flip /
phase-flip codes. -/
theorem shorCode_satisfiesQECConditions :
    SatisfiesQECConditions shorCodeProj shorErrorFamily := sorry

end AxQM
