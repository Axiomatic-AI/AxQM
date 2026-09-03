/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ProjectorHamiltonian
import AxQM.Basic.API.PureState
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# AxQM.Basic.API — the continuous-time search Hamiltonian

The construction behind Nielsen & Chuang's **quantum-search-as-simulation**
picture (§6.2, and the multiple-solution generalisation of Exercise 6.11): the two-projector
Hamiltonian

## Main declarations
* `PureState.searchHamiltonian a ψ` — the Hamiltonian `|a⟩⟨a| + |ψ⟩⟨ψ|` as an `Observable`
  (self-adjoint as a sum of two projector observables).
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The continuous-time search Hamiltonian** `H = |a⟩⟨a| + |ψ⟩⟨ψ|` (Nielsen & Chuang eq. 6.18)
of a target pure state `a` and a starting pure state `ψ`, as an `Observable`. It is the sum of the
two projector Hamiltonians `a.projObservable` and `ψ.projObservable`, hence self-adjoint. Evolving
`ψ` under `H` rotates it towards `a`; this is the Hamiltonian whose simulation reproduces the
quantum search algorithm. -/
def PureState.searchHamiltonian (a ψ : PureState S) : Observable S where
  op := a.projObservable.op + ψ.projObservable.op
  selfAdjoint := a.projObservable.selfAdjoint.add ψ.projObservable.selfAdjoint

end AxQM
