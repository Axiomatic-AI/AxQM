/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorPhaseSyndrome
import AxQM.ToMathlib.Analysis.InnerProductSpace.RankOneProjector

/-!
# AxQM.Basic.API — the Shor-code logical codewords and code projector

Infrastructure for the **code projector** of the nine-qubit Shor code (Nielsen &
Chuang §10.2), the object `P` that N&C's quantum error-correction conditions are
stated with: `P Eᵢ† Eⱼ P = αᵢⱼ P`. It is the first piece of the verification of the QEC conditions
for the Shor code.

## Contents

* `shorCodeword` — the two logical codewords.
* `shorCodeProj` — the code projector `P = |0_L⟩⟨0_L| + |1_L⟩⟨1_L|`.
-/

open scoped InnerProductSpace TensorProduct
open InnerProductSpace

noncomputable section

namespace AxQM

/-- **The Shor logical codewords** `|0_L⟩ = shorCodeword 0` and `|1_L⟩ = shorCodeword 1`, the
equal-sign three-block cat products `shorCatProduct s s s`: three copies of the same block sign.
`shorCodeword 0 = |0_L⟩` uses the `+`-sign block `(|000⟩+|111⟩)/√2`, `shorCodeword 1 = |1_L⟩` the
`−`-sign block `(|000⟩−|111⟩)/√2`. -/
def shorCodeword (s : Fin 2) : PureState shorReg := shorCatProduct s s s

/-- **The Shor code projector** `P = |0_L⟩⟨0_L| + |1_L⟩⟨1_L|`, the orthogonal projector onto the
two-dimensional code space `span{|0_L⟩, |1_L⟩}`. This is the projector `P` of N&C's quantum
error-correction conditions `P Eᵢ† Eⱼ P = αᵢⱼ P`. -/
def shorCodeProj : shorReg.space →L[ℂ] shorReg.space :=
  orthonormalProjector ℂ (fun s => (shorCodeword s).vec) Finset.univ

end AxQM
