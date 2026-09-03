/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorCodeProjector

/-!
# AxQM.Basic.API — the Shor-code stabilizer generators of Figure 10.11

The six bit-flip (Z-type) **stabilizer** generators of the nine-qubit Shor code (Nielsen &
Chuang §10.5.6, Figure 10.11).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **`g₁ = Z₁Z₂`** of Figure 10.11: `Z₁Z₂` on block 1, identity on blocks 2, 3. -/
def shorZ12 : Observable shorReg :=
  zzIObservable ⊗ (Observable.id bitFlipReg ⊗ Observable.id bitFlipReg)

/-- **`g₂ = Z₂Z₃`** of Figure 10.11: `Z₂Z₃` on block 1, identity on blocks 2, 3. -/
def shorZ23 : Observable shorReg :=
  izzObservable ⊗ (Observable.id bitFlipReg ⊗ Observable.id bitFlipReg)

/-- **`g₃ = Z₄Z₅`** of Figure 10.11: identity on block 1, `Z₁Z₂` on block 2, identity on block 3. -/
def shorZ45 : Observable shorReg :=
  Observable.id bitFlipReg ⊗ (zzIObservable ⊗ Observable.id bitFlipReg)

/-- **`g₄ = Z₅Z₆`** of Figure 10.11: identity on block 1, `Z₂Z₃` on block 2, identity on block 3. -/
def shorZ56 : Observable shorReg :=
  Observable.id bitFlipReg ⊗ (izzObservable ⊗ Observable.id bitFlipReg)

/-- **`g₅ = Z₇Z₈`** of Figure 10.11: identity on blocks 1, 2, `Z₁Z₂` on block 3. -/
def shorZ78 : Observable shorReg :=
  Observable.id bitFlipReg ⊗ (Observable.id bitFlipReg ⊗ zzIObservable)

/-- **`g₆ = Z₈Z₉`** of Figure 10.11: identity on blocks 1, 2, `Z₂Z₃` on block 3. -/
def shorZ89 : Observable shorReg :=
  Observable.id bitFlipReg ⊗ (Observable.id bitFlipReg ⊗ izzObservable)

end AxQM
