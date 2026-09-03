/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ContinuousSearchHamiltonian
import AxQM.Basic.API.SymmetricTrotterError

/-!
# AxQM.Basic.API — the off-diagonal coupling Hamiltonian `H = |a⟩⟨ψ| + |ψ⟩⟨a|`

Nielsen & Chuang's **alternative** quantum-search Hamiltonian `H = |a⟩⟨ψ| + |ψ⟩⟨a|`.

## Main declarations
* `PureState.couplingHamiltonian a ψ` — the Hamiltonian `|a⟩⟨ψ| + |ψ⟩⟨a|` as an `Observable`.
* `PureState.couplingProjectorHamiltonians` — the decomposition of `H` into the three projector
  Hamiltonians `|a+ψ⟩⟨a+ψ|`, `−|a⟩⟨a|`, `−|ψ⟩⟨ψ|`, as an ordered list of `Observable`s.
* `PureState.couplingSymmTrotterStep` — the symmetric (Strang) Trotter simulation step of `H`
  (N&C eq. 4.106) built from those three projector propagators.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The off-diagonal coupling Hamiltonian** `H = |a⟩⟨ψ| + |ψ⟩⟨a|` (Nielsen & Chuang,
Exercise 6.12, eq. 6.29) of a target pure state `a` and a starting pure state `ψ`, as an
`Observable`. This is the "alternative Hamiltonian" whose evolution Exercise 6.12 analyses. -/
def PureState.couplingHamiltonian (a ψ : PureState S) : Observable S where
  op := rankOne ℂ a.vec ψ.vec + rankOne ℂ ψ.vec a.vec
  selfAdjoint := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, map_add, adjoint_rankOne,
      adjoint_rankOne]
    exact add_comm _ _

/-- **A rank-one self-projector `|v⟩⟨v|` is self-adjoint.** -/
theorem isSelfAdjoint_rankOne_self (v : S.space) : IsSelfAdjoint (rankOne ℂ v v) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]

/-- **The three projector Hamiltonians simulating the coupling Hamiltonian** (Nielsen & Chuang,
Exercise 6.12(2)). The ordered list of the three rank-one projector Hamiltonians of the
decomposition `H = |a+ψ⟩⟨a+ψ| − |a⟩⟨a| − |ψ⟩⟨ψ|`, each a bona fide `Observable` (self-adjoint
operator). -/
def PureState.couplingProjectorHamiltonians (a ψ : PureState S) : List (Observable S) :=
  [ ⟨rankOne ℂ (a.vec + ψ.vec) (a.vec + ψ.vec), isSelfAdjoint_rankOne_self _⟩,
    ⟨-rankOne ℂ a.vec a.vec, (isSelfAdjoint_rankOne_self _).neg⟩,
    ⟨-rankOne ℂ ψ.vec ψ.vec, (isSelfAdjoint_rankOne_self _).neg⟩ ]

/-- **The symmetric (Strang) Trotter simulation step of the coupling Hamiltonian** (Nielsen &
Chuang, Exercise 6.12(2), which asks for a quantum simulation of `H`). The
palindromic product `Observable.symmTrotterStep` (N&C eq. 4.106) of the propagators of the three
projector Hamiltonians `|a+ψ⟩⟨a+ψ|`, `−|a⟩⟨a|`, `−|ψ⟩⟨ψ|` (`couplingProjectorHamiltonians`).
Repeated `m` times with a small time-step `Δt`, this simulates the true evolution `exp(−2imHΔt)`
to third order in `Δt`. -/
def PureState.couplingSymmTrotterStep (a ψ : PureState S) (Δt : ℝ) : Evolution S :=
  Observable.symmTrotterStep (a.couplingProjectorHamiltonians ψ) Δt

end AxQM
