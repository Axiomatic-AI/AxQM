/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SchmidtNumber
import AxQM.Basic.API.SchmidtDecomposition

/-!
# Nielsen & Chuang, Problem 2.2 (Properties of the Schmidt number)

*(N&C p. 117.)*

Properties of the Schmidt number: rank of rho^A, subadditivity over decompositions,
Sch(psi)>=|Sch(phi)-Sch(gamma)|.

* `schmidtNumber_eq_rank_reducedLeft`
-/

open scoped InnerProductSpace

namespace AxQM

variable {S T : QSystem}

/-- **Problem 2.2(1).** The Schmidt number of a bipartite pure state `|ψ⟩` equals the rank of its
left reduced density operator `ρᴬ = tr_B(|ψ⟩⟨ψ|)`.
-/
theorem PureState.schmidtNumber_eq_rank_reducedLeft (ψ : PureState (S ⊗ T)) :
    ψ.schmidtNumber = ψ.toState.reducedLeft.rank := sorry

end AxQM
