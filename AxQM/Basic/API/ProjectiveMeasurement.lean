/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Measurement
import AxQM.ToMathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# AxQM — projective measurements (N&C §2.2.5 / Exercise 2.62)

A **projective (von Neumann) measurement** is the special case of a general
measurement (`Measurement`) in which the measurement
operators are *orthogonal projectors*. Nielsen–Chuang §2.2.5 describes it by projectors `Pₘ`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- A measurement is **projective** (von Neumann) when every operator `Mᵢ` is a star projection
(`IsStarProjection` — a self-adjoint idempotent, an orthogonal projector). This is the single
minimal condition carving out the projective measurements among all general
measurements: the remaining defining data of N&C §2.2.5 — `Pₘ Pₘ' = δₘₘ' Pₘ`, `∑ₘ Pₘ = I` — is
then automatic for any `Measurement` whose operators are projectors. -/
def IsProjective (m : Measurement ι S) : Prop := ∀ i, IsStarProjection (m.op i)

/-- The measurement operators **coincide with their POVM effects**: `Mᵢ = Eᵢ = Mᵢ† Mᵢ` for every
outcome (N&C Exercise 2.62 hypothesis). Equivalently the induced POVM `toPOVM` has the operators
themselves as its elements. -/
def IsSelfPOVM (m : Measurement ι S) : Prop := ∀ i, m.op i = m.toPOVM.elements i

end Measurement

end AxQM
