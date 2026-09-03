/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Support
import AxQM.Basic.API.Mixture
import AxQM.Basic.API.RelativeEntropy
import AxQM.Basic.API.EntropyComposite
import AxQM.ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.ReducedState
import AxQM.Basic.API.EntropyOrthogonalMixture

/-!
# AxQM — vocabulary for the Araki–Lieb equality conditions

Nielsen & Chuang's Exercise 11.16 characterises when the triangle (Araki–Lieb) inequality
`S(A, B) ≥ S(B) − S(A)` is saturated, in terms of the marginals `ρ^A_i = tr_B(|i⟩⟨i|)` and
`ρ^B_i = tr_A(|i⟩⟨i|)` of the eigenprojectors of `ρ^{AB}`. This file supplies the two
predicates that phrasing needs: "the `ρ^A_i` have a common eigenbasis" and "the `ρ^B_i` have
orthogonal support".

## Main definitions

* `AxQM.State.HasCommonEigenbasis` — a finite family of states `ρ : ι → State S` is
  simultaneously diagonalisable: there is a single orthonormal basis `e` of `S.space` every vector
  of which is an eigenvector (real eigenvalue) of every `ρ i`. This is the precise reading of
  N&C's "the operators `ρ^A_i` have a common eigenbasis".
* `AxQM.State.OrthogonalSupports` — a finite family `ρ : ι → State S` has pairwise
  orthogonal supports, `(ρ i).support ⟂ (ρ j).support` for `i ≠ j` (`State.support`, the range of
  the density operator). N&C's "the `ρ^B_i` have orthogonal support".
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **A finite family of states has a common eigenbasis** — it is simultaneously diagonalisable.
There exists an **orthonormal basis** of `S.space` (a family `e : Fin n → S.space` that is
orthonormal and spans, `Submodule.span ℂ (Set.range e) = ⊤`) every vector `e k` of which is an
eigenvector, with a real eigenvalue, of *every* member `ρ i`: `(ρ i).op (e k) = c • e k`. This is
the precise reading of Nielsen & Chuang's phrase "the operators `ρ^A_i` have a common
eigenbasis". -/
def State.HasCommonEigenbasis {ι : Type*} (ρ : ι → State S) : Prop :=
  ∃ (n : ℕ) (e : Fin n → S.space), Orthonormal ℂ e ∧ Submodule.span ℂ (Set.range e) = ⊤ ∧
    ∀ (i : ι) (k : Fin n), ∃ c : ℝ, (ρ i).op (e k) = (c : ℂ) • e k

/-- **A finite family of states has pairwise orthogonal supports.** For `i ≠ j` the supports
`(ρ i).support`, `(ρ j).support` (the ranges of the density operators, `State.support`) are
orthogonal submodules. Nielsen & Chuang's "the `ρ^B_i` have orthogonal support". -/
def State.OrthogonalSupports {ι : Type*} (ρ : ι → State S) : Prop :=
  Pairwise fun i j => (ρ i).support ⟂ (ρ j).support

end AxQM
