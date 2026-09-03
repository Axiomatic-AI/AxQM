/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import AxQM.ToMathlib.Analysis.InnerProductSpace.OrthonormalDistanceSum
import AxQM.Basic.API.Reflection
import AxQM.Basic.API.ProjectiveMeasurement

/-!
# AxQM.Basic.API — the physical form of the search-optimality lower bound

The search-optimality setting of Nielsen & Chuang §6.6 and **Exercise 6.16**, over the primitives
`QSystem`/`PureState`/`Evolution`/`Measurement`.

## Main declarations

* `searchQueryPureState` — the with-oracle state `ψˣ_k` as a `PureState`.
* `QuantumSearchProblem` — a register with a marked computational basis, together with the marked
  states, the computational-basis `Measurement` and the with-oracle algorithm state.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The with-oracle search state** `ψˣ_k = U_k Oₓ ⋯ U₁ Oₓ ψ` after `k` oracle queries against the
marked pure state `v`, as a `PureState S` (N&C eq. 6.38). -/
def searchQueryPureState (U : ℕ → Evolution S) (ψ v : PureState S) : ℕ → PureState S
  | 0 => ψ
  | j + 1 => (U j).evolvePure ((reflectionEvolution v).evolvePure (searchQueryPureState U ψ v j))

/-- **A quantum-search problem** on the register `S` with `N` items: an orthonormal computational
basis `|x⟩` (`x : Fin N`) of `S.space`, the states one searches among. From it the marked states,
the computational-basis `Measurement` and the with-oracle algorithm state of Nielsen & Chuang §6.6
are derived. -/
structure QuantumSearchProblem (S : QSystem) (N : ℕ) where
  /-- The marked computational basis `|x⟩` of the search register. -/
  markBasis : OrthonormalBasis (Fin N) ℂ S.space

namespace QuantumSearchProblem

variable {N : ℕ} (prob : QuantumSearchProblem S N)

/-- The **marked pure state** `|x⟩` for item `x`: the `x`-th computational-basis vector. -/
def markedState (x : Fin N) : PureState S :=
  ⟨prob.markBasis x, prob.markBasis.orthonormal.norm_eq_one x⟩

/-- The **computational-basis measurement**: the projective `Measurement` in the marked basis
`|x⟩`, whose outcome `x` is "the search returned item `x`" (N&C's step-4 measurement). Its Born
probability is `p(x | ρ) = |⟨x|ρ|x⟩|`. -/
def measurement : Measurement (Fin N) S := Measurement.ofOrthonormalBasis prob.markBasis

/-- **The with-oracle algorithm state** `ψˣ_k` for marked item `x` after `k` queries with unitary
schedule `U` from the initial state `ψ`: `searchQueryPureState` about the marked state `|x⟩`. -/
def queryState (U : ℕ → Evolution S) (ψ : PureState S) (k : ℕ) (x : Fin N) : PureState S :=
  searchQueryPureState U ψ (prob.markedState x) k

end QuantumSearchProblem

end AxQM
