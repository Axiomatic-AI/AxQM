/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuditTensorFactor

/-!
# AxQM.Basic.API — reindexing a qudit across an equality of dimensions

Two qudit systems `qudit d` and `qudit e` whose dimensions are *propositionally* equal (`d = e`)
but not *definitionally* so — e.g. `qudit (2^(n+1))` and `qudit (2 * 2^n)` (`pow_succ'`), or
`qudit (2^(n+2))` and `qudit (2 * 2^(n+1))` — are distinct types, so a term of one cannot be used
where the other is expected. This file supplies the **system isomorphism** reconciling them.

## Main declarations
* `quditDimCongr h` — for `h : d = e`, the system isomorphism `qudit d ≃ₛ qudit e`, built as the
  `OrthonormalBasis.equiv` sending the computational basis `quditOrthonormalBasis d` to
  `quditOrthonormalBasis e` along `finCongr h : Fin d ≃ Fin e`; packaged as a `QSystem.Iso`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {d e : ℕ}

/-- **Reindexing a qudit across an equality of dimensions** `qudit d ≃ₛ qudit e` for `h : d = e`. -/
def quditDimCongr (h : d = e) : (qudit d) ≃ₛ (qudit e) :=
  ⟨(quditOrthonormalBasis d).equiv (quditOrthonormalBasis e) (finCongr h)⟩

end AxQM
