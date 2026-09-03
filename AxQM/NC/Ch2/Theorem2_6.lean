/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.UnitaryFreedom

/-!
# Nielsen & Chuang, Theorem 2.6 (Unitary freedom in the ensemble for density matrices)

*(N&C p. 103.)*

Unitary freedom in the ensemble: two sets generate the same density matrix iff unitarily related.

* `toState_eq_iff_unitarilyRelated`
-/

namespace AxQM

variable {S : QSystem}

/-- **Nielsen–Chuang Theorem 2.6 (unitary freedom in the ensemble).** Two ensembles `e`, `f` of a
quantum system `S`, of the same size (`e.card = f.card` — the padded form, obtained by padding the
smaller ensemble with probability-zero entries), give rise to the same quantum state
`e.toState = f.toState` **if and only if** they are unitarily related (`Ensemble.UnitarilyRelated`):
their subnormalized state vectors `√pᵢ|ψᵢ⟩` are related by a unitary coefficient matrix,
`√pᵢ|ψᵢ⟩ = ∑ⱼ uᵢⱼ √qⱼ|φⱼ⟩` (N&C eq. (2.167)). -/
theorem Ensemble.toState_eq_iff_unitarilyRelated {e f : Ensemble S} (hcard : e.card = f.card) :
    e.toState = f.toState ↔ e.UnitarilyRelated f := sorry

end AxQM
