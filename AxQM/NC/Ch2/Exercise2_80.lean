/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SchmidtDecomposition
import AxQM.Basic.API.Evolution
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Nielsen & Chuang, Exercise 2.80 (identical Schmidt coefficients ⇒ related by `U ⊗ V`)

*(N&C p. 111.)*

Two states with identical Schmidt coefficients related by (U⊗V).

* `exists_evolution_tmul_of_sameSchmidtCoeffs`
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Nielsen & Chuang, Exercise 2.80.** Two bipartite pure states `ψ`, `φ` with identical Schmidt
coefficients (`PureState.SameSchmidtCoeffs`) are related by a **local unitary**: there exist
evolutions `U` on `S` and `V` on `T` with `ψ = (U ⊗ V) φ`.
-/
theorem PureState.exists_evolution_tmul_of_sameSchmidtCoeffs {ψ φ : PureState (S ⊗ T)}
    (h : ψ.SameSchmidtCoeffs φ) :
    ∃ (U : Evolution S) (V : Evolution T), ψ = (U ⊗ V).evolvePure φ := sorry

end AxQM
