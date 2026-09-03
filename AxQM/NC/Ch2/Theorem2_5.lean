/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Ensemble

/-!
# Nielsen & Chuang, Theorem 2.5 (Characterization of density operators)

*(N&C p. 101.)*

Characterization of density operators: rho is a density operator iff trace one and positive.

* `toState_surjective`
-/

namespace AxQM

variable {S : QSystem}

/-- **Nielsen–Chuang Theorem 2.5 (characterization of density operators).** The map sending an
ensemble of pure states `{pᵢ, |ψᵢ⟩}` to its density operator `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` is surjective onto
the states: every quantum state (a positive operator of trace one) arises from an ensemble. -/
theorem Ensemble.toState_surjective :
    Function.Surjective (Ensemble.toState (S := S)) := sorry

end AxQM
