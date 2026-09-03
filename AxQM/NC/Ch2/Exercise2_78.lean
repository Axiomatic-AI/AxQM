/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.ToMathlib.Analysis.InnerProductSpace.Matricization
import AxQM.Basic.API.SchmidtNumber
import AxQM.Basic.Composite
import AxQM.NC.Ch2.Problem2_2
import AxQM.NC.Ch2.Exercise2_74

/-!
# Nielsen & Chuang, Exercise 2.78 (product states, Schmidt number 1, and pure marginals)

*(N&C p. 110.)*

Prove |psi> is a product state iff Schmidt number 1 iff rho^A pure.

* `IsProduct` — the separability predicate `∃ a b, ψ = a ⊗ b`, phrased over `PureState.tmul`.
* `isProduct_iff_schmidtNumber_eq_one` — `|ψ⟩` is a product state ↔ `Sch(ψ) = 1`.
* `isProduct_iff_isPure_reducedLeft` — `|ψ⟩` is a product state ↔ `ρᴬ` is pure.
* `isProduct_iff_isPure_reducedRight` — `|ψ⟩` is a product state ↔ `ρᴮ` is pure.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- A bipartite pure state `|ψ⟩` of `S ⊗ T` is a **product state** when it factors as `|a⟩|b⟩` for
pure states `a` of `S` and `b` of `T` — i.e. `ψ = a ⊗ b` (`PureState.tmul`). -/
def PureState.IsProduct (ψ : PureState (S ⊗ T)) : Prop :=
  ∃ (a : PureState S) (b : PureState T), ψ = a.tmul b

/-- **Nielsen & Chuang, Exercise 2.78 (first equivalence).** A bipartite pure state `|ψ⟩` is a
product state if and only if it has Schmidt number `1`. -/
theorem PureState.isProduct_iff_schmidtNumber_eq_one (ψ : PureState (S ⊗ T)) :
    ψ.IsProduct ↔ ψ.schmidtNumber = 1 := sorry

/-- **Nielsen & Chuang, Exercise 2.78 (second equivalence).** A bipartite pure state `|ψ⟩` is a
product state if and only if its reduced density operator `ρᴬ = tr_B(|ψ⟩⟨ψ|)` is pure. -/
theorem PureState.isProduct_iff_isPure_reducedLeft (ψ : PureState (S ⊗ T)) :
    ψ.IsProduct ↔ ψ.toState.reducedLeft.IsPure := sorry

/-- **Nielsen & Chuang, Exercise 2.78 (second equivalence, `ρᴮ` form — the "and thus `ρᴮ`").** A
bipartite pure state `|ψ⟩` is a product state if and only if its reduced density operator `ρᴮ =
tr_A(|ψ⟩⟨ψ|)` is pure. -/
theorem PureState.isProduct_iff_isPure_reducedRight (ψ : PureState (S ⊗ T)) :
    ψ.IsProduct ↔ ψ.toState.reducedRight.IsPure := sorry

end AxQM
