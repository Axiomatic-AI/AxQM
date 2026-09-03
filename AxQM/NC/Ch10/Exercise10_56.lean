/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Exercise10_52
import AxQM.Basic.API.CSSCode

/-!
# Nielsen & Chuang, Exercise 10.56 — a stabilizer factor doesn't change an encoded operator's action

*(N&C p. 471.)*

Replacing encoded X or Z operator by g times it (g in stabilizer) doesn't change its action on the
code.

* `evolvePure_comp_eq_of_commute_hasEigenstate_one` — Exercise 10.56, general form: for any
  evolutions `g, L` on a system `S` with `Commute g L` and `g.HasEigenstate 1 ψ` (a code state),
  `(g.comp L).evolvePure ψ = L.evolvePure ψ`.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 10.56 (general form).** Replacing an operator `L` by `g·L`, where
`g` **commutes** with `L` and **fixes** the state `ψ` (i.e. `ψ` is a `+1` eigenstate of `g`),
does not change its action on `ψ`: `(g·L)|ψ⟩ = L|ψ⟩`. -/
theorem evolvePure_comp_eq_of_commute_hasEigenstate_one {S : QSystem} {g L : Evolution S}
    {ψ : PureState S} (hcomm : Commute g L) (hfix : g.HasEigenstate 1 ψ) :
    (g.comp L).evolvePure ψ = L.evolvePure ψ := sorry

end AxQM
