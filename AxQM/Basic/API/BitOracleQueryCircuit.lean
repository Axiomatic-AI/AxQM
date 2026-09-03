/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# AxQM.Basic.API — the bit-oracle query circuit

Physical representative for the **method of polynomials** (Nielsen & Chuang §6.7, eqs. 6.58–6.61,
Figure 6.10), the tool Exercise 6.20 uses to prove `Q₀(OR) ≥ N`. This file grounds the *circuit*
side of the method in the primitives `QSystem`/`PureState`/`Evolution`: the bit-oracle
`O_X` as a genuine unitary `Evolution` family, and the `T`-query algorithm state `ψ(X)` as a genuine
`PureState`.

## Main declarations

* `bitFlip X` / `bitFlipPerm X` — the answer-qubit XOR map `(i, b, j) ↦ (i, b ⊕ Xᵢ, j)` on
  `σ × Bool × ω`, and its packaging as an `Equiv.Perm` (built from its own involutivity).
* `QuantumQueryProblem S σ ω` — a register `S` with a computational basis indexed by `σ × Bool × ω`;
  `basisState p` is the computational-basis vector `|p⟩` as a `PureState`.
* `QuantumQueryProblem.bitOracle X` — the bit-oracle `O_X` as a unitary `Evolution S`
  (`Evolution.ofLinearIsometryEquiv` of the basis permutation), acting as
  `O_X |i,b,j⟩ = |i, b ⊕ Xᵢ, j⟩`.
* `queryPureState` / `QuantumQueryProblem.queryState` — the `T`-query algorithm state `ψ(X)` as a
  genuine `PureState`, by `Evolution.evolvePure` recursion (`U₀` first, then each step reflects by
  `O_X` and applies `U_{t+1}`).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem} {σ ω : Type*}

/-- The **answer-qubit XOR map** `(i, b, j) ↦ (i, b ⊕ Xᵢ, j)` on the computational-basis labels
`σ × Bool × ω`, for a bit-string `X : σ → Bool`. It flips the answer qubit `b` by the queried bit
`Xᵢ` and leaves the query index `i` and workspace `j` untouched — the label action of Nielsen &
Chuang's bit-oracle (eq. 6.61). -/
def bitFlip (X : σ → Bool) (p : σ × Bool × ω) : σ × Bool × ω :=
  (p.1, xor p.2.1 (X p.1), p.2.2)

/-- The bit-flip map is an **involution**. This is what makes the bit-oracle a self-inverse unitary.
-/
theorem bitFlip_involutive (X : σ → Bool) : Function.Involutive (bitFlip (ω := ω) X) := by
  rintro ⟨i, b, j⟩
  simp only [bitFlip, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The **answer-qubit XOR permutation** `bitFlipPerm X : Equiv.Perm (σ × Bool × ω)`, packaging the
involution `bitFlip X` as a permutation of the computational-basis labels. This is the permutation
the bit-oracle realises on the basis. -/
def bitFlipPerm (X : σ → Bool) : Equiv.Perm (σ × Bool × ω) :=
  (bitFlip_involutive X).toPerm

/-- **A quantum-query problem** on the register `S`: an orthonormal computational basis `|i,b,j⟩` of
`S.space` indexed by `σ × Bool × ω` — the oracle-query index `i`, the single answer qubit `b`, and
the workspace `j` of Nielsen & Chuang's Figure 6.10. It packages the register so the bit-oracle
family and the query state can be stated over the primitives, mirroring Exercise 6.16's
`QuantumSearchProblem`. -/
structure QuantumQueryProblem (S : QSystem) (σ ω : Type*) [Fintype σ] [Fintype ω] where
  /-- The computational basis `|i,b,j⟩` of the query register, indexed by `σ × Bool × ω`. -/
  basis : OrthonormalBasis (σ × Bool × ω) ℂ S.space

namespace QuantumQueryProblem

variable [Fintype σ] [Fintype ω] (prob : QuantumQueryProblem S σ ω)

/-- **The bit-oracle** `O_X` for the bit-string `X : σ → Bool` (Nielsen & Chuang, eq. 6.61). -/
def bitOracle (X : σ → Bool) : Evolution S :=
  Evolution.ofLinearIsometryEquiv (prob.basis.equiv prob.basis (bitFlipPerm X))

end QuantumQueryProblem

/-- **The query algorithm state** `ψ_t = U_t O ⋯ O U₀ ψ₀` after `t` oracle queries against the
oracle `O`, with unitary schedule `U : ℕ → Evolution S` and input `ψ`, as a genuine `PureState
S`. -/
def queryPureState (O : Evolution S) (U : ℕ → Evolution S) (ψ : PureState S) : ℕ → PureState S
  | 0 => (U 0).evolvePure ψ
  | t + 1 => (U (t + 1)).evolvePure (O.evolvePure (queryPureState O U ψ t))

namespace QuantumQueryProblem

variable [Fintype σ] [Fintype ω] (prob : QuantumQueryProblem S σ ω)

/-- **The `T`-query algorithm state** `ψ(X)_t = U_t O_X ⋯ O_X U₀ ψ` for the bit-string `X` after `t`
queries, with unitary schedule `U` and input `ψ`: `queryPureState` driven by the bit-oracle
`prob.bitOracle X`. -/
def queryState (U : ℕ → Evolution S) (ψ : PureState S) (X : σ → Bool) (t : ℕ) : PureState S :=
  queryPureState (prob.bitOracle X) U ψ t

end QuantumQueryProblem

end AxQM
