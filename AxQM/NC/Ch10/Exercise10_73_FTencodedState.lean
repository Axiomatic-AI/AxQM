/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Exercise10_63
import AxQM.Basic.API.CSSCodeSpace
import AxQM.Concrete.SteaneCode

/-!
# Nielsen & Chuang, Exercise 10.73 — fault-tolerant construction of the Steane encoded `|0⟩`

*(N&C p. 493.)*

Show the Steane code encoded |0> can be constructed fault-tolerantly (cat-state ancillas, verify,
error prob).

* `steaneZeroStabilizer`
* `steaneZeroStabilizer_hasEigenstate_one_logicalZero` — the target `|0_L⟩` is a common
  `+1`-eigenstate of all seven observables `⟨g₁,…,g₆, Z̄⟩`;
* `steaneLogicalZero_eq_of_stabilized` — `|0_L⟩` is the only such state, up to a global phase.
-/

noncomputable section

namespace AxQM

open AxQM.Concrete

/-- **The seven stabilizer generators of the Steane encoded `|0⟩`.** The observables measured in the
fault-tolerant preparation of `|0_L⟩` (Exercise 10.73): the six code stabilizer generators
`steaneStabilizer` of Figure 10.6 (`g₁,…,g₆`, indices `0–5`) followed by the encoded logical-`Z̄`
operator `steaneLogicalZBar` (index `6`). Together they generate the full stabilizer group
`⟨g₁,…,g₆, Z̄⟩` of the *state* `|0_L⟩` (seven independent generators on seven qubits), as opposed to
the six-generator stabilizer of the two-dimensional code. -/
def steaneZeroStabilizer : Fin 7 → Evolution (bitReg (Fin 7)) :=
  Fin.snoc steaneStabilizer steaneLogicalZBar

/-- **The encoded `|0⟩` passes every measurement of the construction.** The Steane logical zero
`|0_L⟩` is a common `+1`-eigenstate of all seven observables `steaneZeroStabilizer` — the six
Figure-10.6 generators and the encoded `Z̄`. Physically: `|0_L⟩` realises the all-`+1` measurement
outcome that the fault-tolerant construction post-selects. -/
theorem steaneZeroStabilizer_hasEigenstate_one_logicalZero (i : Fin 7) :
    (steaneZeroStabilizer i).HasEigenstate 1 steaneLogicalZero := sorry

/-- **The construction prepares exactly the encoded `|0⟩` (uniqueness).** Any state `ψ` that is a
common `+1`-eigenstate of *all seven* observables `steaneZeroStabilizer` — the six Figure-10.6
generators `g₁,…,g₆` **and** the encoded `Z̄` — equals the logical zero `|0_L⟩` up to a global
phase. -/
theorem steaneLogicalZero_eq_of_stabilized (ψ : PureState (bitReg (Fin 7)))
    (hfix : ∀ i, (steaneZeroStabilizer i).HasEigenstate 1 ψ) :
    ψ.toState = steaneLogicalZero.toState := sorry

end AxQM
