/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SchmidtNumber

/-!
# Nielsen & Chuang, Exercise 2.76 (Schmidt decomposition for unequal dimensions)

*(N&C p. 110.)*

Extend the Schmidt decomposition proof to unequal-dimension A and B.

* `schmidtNumber_le_dim` — the Schmidt number is at most `min S.dim T.dim`.
-/

open scoped InnerProductSpace

namespace AxQM

variable {S T : QSystem}

/-- **Schmidt number bound for unequal subsystem dimensions (Nielsen–Chuang Exercise 2.76).** The
Schmidt number of a bipartite pure state `|ψ⟩` — the number of nonzero Schmidt coefficients in
`|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩` — is at most the smaller of the two subsystem dimensions, `Sch(ψ) ≤
min(dim A, dim B)`.

This is the content of Exercise 2.76, which extends the Schmidt decomposition to
`dim A ≠ dim B`.
-/
theorem PureState.schmidtNumber_le_dim (ψ : PureState (S ⊗ T)) :
    ψ.schmidtNumber ≤ min S.dim T.dim := sorry

end AxQM
