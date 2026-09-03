/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuditPairPermGate
import AxQM.Basic.API.QuditMeasurement
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.SystemIso

/-!
# AxQM.Basic.API — factoring a qudit of composite dimension

A `d·e`-level system is a *bipartite* system: `qudit (d·e) ≃ₛ qudit d ⊗ qudit e`, identifying the
computational basis `|x·e + y⟩` of the single register with the product basis `|x⟩ ⊗ |y⟩` of the
pair.

## Main declarations
* `quditProdIso d e` — the system isomorphism `qudit (d·e) ≃ₛ qudit d ⊗ qudit e`, sending the
  computational basis of `qudit (d·e)` to the product basis of `qudit d ⊗ qudit e` along
  `finProdFinEquiv : Fin d × Fin e ≃ Fin (d·e)`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {d e : ℕ}

/-- **Factoring a composite-dimension qudit** `qudit (d·e) ≃ₛ qudit d ⊗ qudit e`: the system
isomorphism identifying the `d·e`-level register with the bipartite `d`-by-`e` register. -/
def quditProdIso (d e : ℕ) : (qudit (d * e)) ≃ₛ (qudit d ⊗ qudit e) :=
  ⟨(quditOrthonormalBasis (d * e)).equiv (quditPairBasis d e) finProdFinEquiv.symm⟩

end AxQM
