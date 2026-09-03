/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Purity
import AxQM.Basic.API.PureMarginalEntropy

/-!
# Nielsen & Chuang, Theorem 11.8 (Basic properties of von Neumann entropy)

*(N&C p. 513.)*

Basic properties of von Neumann entropy: non-negativity, bound, purity, joint entropy theorem.

* `vonNeumannEntropy_eq_zero_iff_isPure` — Part 1, converse `S(ρ) = 0 ⇒ ρ` pure, and hence the full
  first-item characterization `S(ρ) = 0 ↔ ρ` pure —
  `AxQM.State.vonNeumannEntropy_eq_zero_iff_isPure`.
-/

namespace AxQM

variable {S : QSystem}

/-- **The von Neumann entropy vanishes exactly on pure states** (Nielsen–Chuang Theorem 11.8, part
(1)): `S(ρ) = 0 ↔ ρ` is pure. -/
theorem State.vonNeumannEntropy_eq_zero_iff_isPure (ρ : State S) :
    ρ.vonNeumannEntropy = 0 ↔ ρ.IsPure := sorry

end AxQM
