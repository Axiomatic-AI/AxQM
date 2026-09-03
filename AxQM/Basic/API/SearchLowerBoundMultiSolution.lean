/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.SearchOptimality
import AxQM.Concrete.SearchLowerBoundMultiSolution

/-!
# AxQM.Basic.API — the physical form of the multiple-solution search lower bound

Generators that lift the linear algebra of Nielsen & Chuang **Exercise 6.17** —
the `M`-solution generalisation of the §6.6 optimality proof — onto the primitives
`QSystem`/`PureState`/`Evolution`/`Measurement`.

## Main declarations

* `QuantumSearchProblem.setOracle` — the set oracle `O_s = I − 2 P_s` as an `Evolution S`.
  Unitarity is bundled and discharged from `P_s` being a star projection (self-adjoint idempotent),
  exactly as for the single-item reflection.
* `QuantumSearchProblem.setQueryState` — the with-oracle state `ψˢ_k` as a genuine `PureState S`,
  by recursion through `Evolution.evolvePure`.
-/

open scoped InnerProductSpace
open Finset InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A `k`-query algorithm state with a fixed oracle** `O`. The search-agnostic backbone of
`QuantumSearchProblem.setQueryState` — the oracle is passed explicitly, keeping the recursion
free of the search-problem data. -/
def searchSetQueryState (U : ℕ → Evolution S) (O : Evolution S) (ψ : PureState S) :
    ℕ → PureState S
  | 0 => ψ
  | k + 1 => (U k).evolvePure (O.evolvePure (searchSetQueryState U O ψ k))

namespace QuantumSearchProblem

variable {N : ℕ} (prob : QuantumSearchProblem S N)

/-- **The set oracle** `O_s = I − 2 P_s` for a marked set `s : Finset (Fin N)`: the reflection
about the marked subspace `span{|y⟩ : y ∈ s}`, as a unitary `Evolution S`. It is the `M`-solution
search oracle (N&C's `O|x⟩ = (−1)^{f(x)}|x⟩`, marking every item in `s`); the single-item
`prob.oracle x` is the special case `s = {x}`. Unitarity is bundled and discharged from the marked
projection `P_s = markedProj markBasis s` being a star projection (self-adjoint idempotent), so
`O_s = I − 2 P_s` is a self-adjoint involution, hence unitary. -/
def setOracle (s : Finset (Fin N)) : Evolution S where
  op := Concrete.markedOracle prob.markBasis s
  unitary := by
    haveI : CompleteSpace S.space := FiniteDimensional.complete ℂ S.space
    set P : S.space →L[ℂ] S.space := Concrete.markedProj prob.markBasis s with hPdef
    have hPP : P * P = P :=
      isIdempotentElem_orthonormalProjector prob.markBasis.orthonormal s
    have hPsa : star P = P :=
      isSelfAdjoint_orthonormalProjector (𝕜 := ℂ) (⇑prob.markBasis) s
    have hop : Concrete.markedOracle prob.markBasis s = 1 - (2 : ℂ) • P := by
      rw [hPdef]; rfl
    rw [hop]
    -- `O_s = I − 2P_s` is unitary because `P_s` is a star projection: apply the structural
    -- Mathlib lemma `IsStarProjection.two_mul_sub_one_mem_unitary` to `1 − P_s` (also a star
    -- projection), rewriting `2·(1 − P_s) − 1 = 1 − 2P_s`.
    have hsp : IsStarProjection P := ⟨hPP, hPsa⟩
    have hu := (isStarProjection_one_sub_iff.mpr hsp).two_mul_sub_one_mem_unitary
    have he : (2 : S.space →L[ℂ] S.space) * (1 - P) - 1 = 1 - (2 : ℂ) • P := by
      rw [two_smul, two_mul]; abel
    rwa [he] at hu

/-- **The with-oracle algorithm state** `ψˢ_k = U_{k−1} O_s ⋯ U_0 O_s ψ` for the marked set `s`
after `k` oracle queries with unitary schedule `U` from the initial state `ψ`, as a genuine
`PureState S`. -/
def setQueryState (U : ℕ → Evolution S) (ψ : PureState S) (s : Finset (Fin N)) (k : ℕ) :
    PureState S :=
  searchSetQueryState U (prob.setOracle s) ψ k

end QuantumSearchProblem

end AxQM
