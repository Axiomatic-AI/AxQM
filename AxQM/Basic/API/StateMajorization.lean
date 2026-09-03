/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PseudoInverse
import AxQM.Basic.API.TypicalSubspace
import AxQM.Basic.API.Fidelity
import AxQM.Basic.Measurement
import AxQM.ToMathlib.Analysis.Convex.Majorization
import AxQM.ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl

/-!
# AxQM — majorization of quantum states and the reverse operator-majorization theorem

This is the spectral foundation for **Nielsen's theorem**: a
bipartite pure state `|ψ⟩` can be transformed to `|ϕ⟩` by LOCC iff `λ_ψ ≺ λ_ϕ`, where `λ_ψ` is the
vector of squared Schmidt coefficients — equivalently the eigenvalues of the reduced density
operator `ρ_ψ`. The condition `λ_ψ ≺ λ_ϕ` is *majorization of the reduced states*, which we make
first-class here.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace State

/-- **Majorization of quantum states.** `ρ.Majorize σ` (N&C's `ρ ≺ σ` for density operators) holds
when the eigenvalue distribution of `ρ` is majorized by that of `σ` (`Majorize` on the eigenvalue
vectors). This is the exact condition `λ_ψ ≺ λ_ϕ` of Nielsen's theorem when `ρ`, `σ` are the reduced
states of bipartite pure states. -/
def Majorize (ρ σ : State S) : Prop :=
  _root_.Majorize ρ.eigenvalueDist σ.eigenvalueDist

/-- **One-way LOCC convertibility of reduced states** (the standard protocol form, N&C Proposition
12.14).

Operationally (Nielsen's theorem, N&C Theorem 12.15). This is the density-operator content —
expressible over the `State`/`Measurement` primitives — of the transformation of `|ψ⟩` to `|φ⟩` by
LOCC. The quantifier over *general* LOCC protocols is a documented fidelity boundary.
-/
def LOCCConvertible (ρ σ : State S) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (m : Measurement ι S) (p : ι → ℝ),
    (∀ j, 0 ≤ p j) ∧ (∑ j, p j = 1) ∧
      ∀ j, (m.op j).comp (ρ.op.comp (adjoint (m.op j))) = (p j : ℂ) • σ.op

/-- **Converse of Nielsen's theorem** (Nielsen–Chuang Theorem 12.15, `⟸`), the reduced-state crux:
if `ρ ≺ σ` then `ρ` can be converted to `σ` by a one-way LOCC measurement. This is the direction
that *constructs* the protocol from the majorization condition, and it needs **no invertibility
hypothesis** on `ρ` (N&C Exercise 12.20).
-/
theorem LOCCConvertible_of_majorize {ρ σ : State S} (h : ρ.Majorize σ) :
    ρ.LOCCConvertible σ := sorry

end State

end AxQM
