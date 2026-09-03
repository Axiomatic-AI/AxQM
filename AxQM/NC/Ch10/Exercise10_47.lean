/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ShorStabilizer

/-!
# Nielsen & Chuang, Exercise 10.47 — the Fig 10.11 generators stabilize the Shor codewords

*(N&C p. 468.)*

Verify generators of Fig 10.11 generate the two Shor-code codewords of (10.13).

* `shorStabilizer`
* `shorStabilizer_hasEigenstate_one_shorCodeword`
-/

namespace AxQM

/-- **The eight stabilizer generators of Figure 10.11**, as a single family
`Fin 8 → Observable shorReg`: the six bit-flip (`Z`-type) generators `g₁,…,g₆` followed by the two
phase-flip (`X`-type) generators `g₇, g₈`. -/
noncomputable def shorStabilizer : Fin 8 → Observable shorReg :=
  ![shorZ12, shorZ23, shorZ45, shorZ56, shorZ78, shorZ89,
    shorPhaseSyndromeX123456, shorPhaseSyndromeX456789]

/-- **Nielsen & Chuang, Exercise 10.47.** Every one of the eight Figure-10.11 generators stabilizes
each Shor logical codeword `|s_L⟩` (eq. (10.13)). -/
theorem shorStabilizer_hasEigenstate_one_shorCodeword (s : Fin 2) (i : Fin 8) :
    (shorStabilizer i).HasEigenstate 1 (shorCodeword s) := sorry

end AxQM
