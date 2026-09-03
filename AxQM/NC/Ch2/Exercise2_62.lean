/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ProjectiveMeasurement

/-!
# Nielsen & Chuang, Exercise 2.62 (self-POVM measurements are projective)

*(N&C p. 92.)*

Show any measurement where measurement operators and POVM elements coincide is projective.

* `isProjective_of_isSelfPOVM`
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **N&C Exercise 2.62.** A measurement whose measurement operators coincide with their POVM
elements (`Mᵢ = Eᵢ = Mᵢ† Mᵢ`, i.e. `Measurement.IsSelfPOVM`) is a projective measurement
(`Measurement.IsProjective`): every `Mᵢ` is an orthogonal projector. -/
theorem Measurement.isProjective_of_isSelfPOVM (m : Measurement ι S) (h : m.IsSelfPOVM) :
    m.IsProjective := sorry

end AxQM
