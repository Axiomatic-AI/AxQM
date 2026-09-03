/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DeutschDoublyControlledReachable
import AxQM.Concrete.MultiControlledSingleQubit

/-!
# Concrete: the three-wire register encoding `(Fin 3 → Fin 2) ≃ Fin 8` (N&C Ex 4.44)
-/

namespace AxQM.Concrete

open Matrix

/-- **A `Fin 3`-indexed bit string as an ordered triple.** The equivalence `(Fin 3 → Fin 2) ≃ Fin 2
× Fin 2 × Fin 2` reading a three-bit string `x` as the triple `(x 0, x 1, x 2)` (and back via
`![·, ·, ·]`). -/
def finThreeArrowProd : (Fin 3 → Fin 2) ≃ (Fin 2 × Fin 2 × Fin 2) where
  toFun x := (x 0, x 1, x 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv x := by
    funext k
    fin_cases k <;> rfl
  right_inv p := rfl

/-- **The canonical three-wire register encoding** `(Fin 3 → Fin 2) ≃ Fin 8`. Reads a three-bit
string as the register index `4·x 0 + 2·x 1 + x 2` — bit `k` of the string is register wire `k`,
packed big-endian exactly as `threeQubitIndex` packs the control/control/target triple
`(c₁, c₂, t)`. -/
def finThreeRegEnc : (Fin 3 → Fin 2) ≃ Fin 8 :=
  finThreeArrowProd.trans threeQubitIndex

end AxQM.Concrete
