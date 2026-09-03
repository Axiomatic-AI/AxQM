/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Observable

/-!
# AxQM.Basic.API — eigenstates of an observable (general)

* `Observable.HasEigenstate A μ ψ` — the pure-state eigenvalue equation `A ψ = μ ψ` of an
  observable, with the eigenvalue `μ : ℝ` explicit (an observable's eigenvalues are its real
  possible measurement values). The surrogate for the raw eigenvalue equation.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **`ψ` is an eigenstate of the observable `A` with eigenvalue `μ`.** The pure-state eigenvalue
equation `A ψ = μ ψ` of an observable, with the eigenvalue `μ : ℝ` explicit (an observable's
eigenvalues are real — its possible measurement values). A reusable physics generator. -/
def Observable.HasEigenstate (A : Observable S) (μ : ℝ) (ψ : PureState S) : Prop :=
  A.op ψ.vec = (μ : ℂ) • ψ.vec

end AxQM
