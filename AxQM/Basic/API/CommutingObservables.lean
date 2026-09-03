/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Observable
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-!
# AxQM.Basic.API — commuting observables

The commutation relation `[A, B] = 0` for a pair of observables.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Two observables commute** (`[A, B] = 0`): their underlying self-adjoint operators
commute. -/
def Observable.Commutes (A B : Observable S) : Prop := Commute A.op B.op

end AxQM
