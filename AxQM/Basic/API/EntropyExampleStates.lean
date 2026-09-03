/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BlochState
import AxQM.Basic.API.PauliEigen
import AxQM.Basic.API.Entropy
import Mathlib.Analysis.InnerProductSpace.PiL2
import AxQM.Concrete.BlochMatrix

/-!
# AxQM.Basic.API — the three density matrices of Nielsen & Chuang Exercise 11.11

The three explicit `2 × 2` density matrices of Exercise 11.11, as `State qubit`s.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

open Matrix

/-- **N&C (11.41):** the density matrix `!![1, 0; 0, 0] = |0⟩⟨0|`, realised as the Bloch state
`blochState ![0, 0, 1] = ½(I + Z)`. -/
def entropyExampleZeroState : State qubit :=
  blochState ![0, 0, 1]
    (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two])

/-- **N&C (11.42):** the density matrix `½ !![1, 1; 1, 1] = |+⟩⟨+|`, realised as the Bloch state
`blochState ![1, 0, 0] = ½(I + X)`. -/
def entropyExamplePlusState : State qubit :=
  blochState ![1, 0, 0]
    (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two])

/-- **N&C (11.43):** the mixed density matrix `⅓ !![2, 1; 1, 1]`, realised as the Bloch state
`blochState ![2/3, 0, 1/3] = ½(I + ⅔X + ⅓Z)`. -/
def entropyExampleMixedState : State qubit :=
  blochState ![2 / 3, 0, 1 / 3]
    (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two])

end AxQM
