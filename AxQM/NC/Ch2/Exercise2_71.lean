/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Purity

/-!
# Nielsen & Chuang, Exercise 2.71 (criterion to decide if a state is mixed or pure)

*(N&C p. 103.)*

Show tr(rho^2)<=1 with equality iff rho is a pure state.

* `purity_le_one` — `tr(ρ²) ≤ 1` for every state.
* `purity_eq_one_iff_isPure` — `tr(ρ²) = 1` if and only if `ρ` is pure.
-/

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 2.71 (the bound).** The purity of any state is at most one: `tr(ρ²)
≤ 1`. -/
theorem State.purity_le_one (ρ : State S) : ρ.purity ≤ 1 := sorry

/-- **Nielsen & Chuang, Exercise 2.71 (the equality case).** A state has purity exactly one iff it
is pure: `tr(ρ²) = 1 ↔ ρ = |ψ⟩⟨ψ|` for some pure state `ψ`. -/
theorem State.purity_eq_one_iff_isPure (ρ : State S) : ρ.purity = 1 ↔ ρ.IsPure := sorry

end AxQM
