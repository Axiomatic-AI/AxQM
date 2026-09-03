/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.Theorem12_15
import AxQM.Basic.API.CatalysisStates

/-!
# Nielsen & Chuang, Exercise 12.21 (Entanglement catalysis)

*(N&C p. 577.)*

Entanglement catalysis: |psi> cannot go to |phi> by LOCC but |psi>|c> can.

* `catalysisState_not_loccConvertible` — `¬ ρ_ψ.LOCCConvertible ρ_φ`: no direct LOCC conversion
  `|ψ⟩ → |φ⟩`;
* `catalysisState_tmul_loccConvertible` — `(ρ_ψ ⊗ ρ_c).LOCCConvertible (ρ_φ ⊗ ρ_c)`: the catalysed
  conversion `|ψ⟩|c⟩ → |φ⟩|c⟩` succeeds, the borrowed entanglement `|c⟩` being returned unchanged.
-/

open AxQM.Concrete

namespace AxQM

/-- **No direct LOCC conversion `|ψ⟩ → |φ⟩`** (N&C Exercise 12.21, first part). The reduced state
`ρ_ψ` cannot be converted to `ρ_φ` by (one-way) LOCC. -/
theorem catalysisState_not_loccConvertible :
    ¬ catalysisStatePsi.LOCCConvertible catalysisStatePhi := sorry

/-- **Catalysed LOCC conversion `|ψ⟩|c⟩ → |φ⟩|c⟩`** (N&C Exercise 12.21, catalysis part). Tensoring
both states with the catalyst `ρ_c` makes the conversion possible: `ρ_ψ ⊗ ρ_c` *can* be
converted to `ρ_φ ⊗ ρ_c` by (one-way) LOCC — the borrowed entanglement `|c⟩` is returned
unchanged. -/
theorem catalysisState_tmul_loccConvertible :
    (catalysisStatePsi.tmul catalysisStateCat).LOCCConvertible
      (catalysisStatePhi.tmul catalysisStateCat) := sorry

end AxQM
