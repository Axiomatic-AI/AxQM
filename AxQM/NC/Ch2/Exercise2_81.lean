/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Composite
import AxQM.Basic.PartialTrace
import AxQM.ToMathlib.Analysis.InnerProductSpace.Purification
import AxQM.ToMathlib.Analysis.InnerProductSpace.EuclideanConjVec
import AxQM.ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl

/-!
# Nielsen & Chuang, Exercise 2.81 (freedom in purifications)

*(N&C p. 111.)*

Freedom in purifications: two purifications related by (I_A⊗U_R).

* `exists_evolution_tmul_id_evolvePure_eq`
-/

open AxQM

namespace AxQM

/-- **Freedom in purifications** (N&C Exercise 2.81). -/
theorem PureState.exists_evolution_tmul_id_evolvePure_eq {S R : QSystem}
    (ψ φ : PureState (S.compose R)) (h : ψ.toState.reducedLeft = φ.toState.reducedLeft) :
    ∃ U : Evolution R, φ = ((Evolution.id (S := S)).tmul U).evolvePure ψ := sorry

end AxQM
