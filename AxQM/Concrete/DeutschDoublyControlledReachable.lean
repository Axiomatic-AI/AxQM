/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DeutschControlledReachable

/-!
# Concrete: doubly-controlled Deutsch gate reaches `C²(R_x β)` and `Toffoli` (N&C Ex 4.44)

For irrational `α`, the closure of the doubly-controlled Deutsch iterates `{C²(iⁿ R_x(nπα))}` — the
doubly-controlled gates `C²(g)`, which fire `g` exactly when both control qubits are `|1⟩`, built
from the powers of the Deutsch target `iR_x(πα)` — contains every doubly-controlled `x`-rotation
`C²(R_x(β))` and the Toffoli gate `C²(X)`.
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

/-- **The packing bijection `Fin 2 × Fin 2 × Fin 2 ≃ Fin 8`** for the right-nested
`Fin 2 × (Fin 2 × Fin 2)` index type: `(c₁, c₂, t) ↦ finProdFinEquiv (c₁,
finProdFinEquiv (c₂, t))`, the big-endian packing `4·c₁ + 2·c₂ + t`. -/
def threeQubitIndex : (Fin 2 × Fin 2 × Fin 2) ≃ Fin 8 :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv

end AxQM.Concrete
