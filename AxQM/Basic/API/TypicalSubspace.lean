/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.TensorPowState
import AxQM.Basic.API.MeasurementModel
import AxQM.Basic.API.Entropy
import AxQM.ToMathlib.InformationTheory.TypicalSequence
import AxQM.ToMathlib.Analysis.InnerProductSpace.EntanglementFidelity

/-!
# AxQM.Basic.API — the ε-typical subspace projector `P(n, ε)` (N&C Thm 12.5)

The infrastructure for Nielsen & Chuang's **typical subspace theorem** (Theorem
12.5): the ε-typical subspace projector `P(n, ε)`, its rank/trace identities, and its realization as
a projective measurement whose Born probability is the classical typicality probability.
-/

open scoped InnerProductSpace TensorProduct BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The **eigenvalue distribution** `λ : Fin d → ℝ` (`d = dim S.space`) of a quantum state `ρ`: the
spectrum of the density operator, indexed by `ρ`'s canonical eigenbasis
(`ρ.isDensity.isSymmetric.eigenvalues`). -/
def State.eigenvalueDist (ρ : State S) : Fin (Module.finrank ℂ S.space) → ℝ :=
  ρ.isDensity.isSymmetric.eigenvalues rfl

/-- The **dimension of the ε-typical subspace** `|T(n, ε)|` (Nielsen & Chuang, Theorem 12.5, part
(2)): the number of ε-typical index sequences `κ ∈ Real.typicalSeq λ n ε`, equivalently the rank of
`P(n, ε)`. -/
def State.typicalSubspaceDim (ρ : State S) (n : ℕ) (ε : ℝ) : ℕ :=
  (Real.typicalSeq ρ.eigenvalueDist n ε).card

/-- **The typical/atypical projective measurement** `{P(n, ε), I − P(n, ε)}` (Nielsen & Chuang,
Theorem 12.5): the two-outcome von Neumann measurement asking whether `ρ^⊗n` lies in the
ε-typical subspace. -/
def State.typicalSubspaceMeasurement (ρ : State S) (n : ℕ) (ε : ℝ) :
    Measurement Bool (S ^⊗ₛ n) :=
  Measurement.ofOrthonormalBasisFiber (ρ.tensorPowEigenbasis n)
    (fun κ => decide (κ ∈ Real.typicalSeq ρ.eigenvalueDist n ε))

/-- The **dimension of the "true"-outcome subspace** of a two-outcome measurement `M` on `S ^⊗ₛ n`:
the rank (`finrank` of the range) of the projector `M.op true` — the dimension quantified over in
the small-subspace bound of the typical subspace theorem (Nielsen & Chuang, Theorem 12.5,
part (3)), "any subspace of dimension at most `2^{nR}`". -/
def Measurement.trueSubspaceDim {n : ℕ} (M : Measurement Bool (S ^⊗ₛ n)) : ℕ :=
  Module.finrank ℂ (LinearMap.range (M.op true : (S ^⊗ₛ n).space →ₗ[ℂ] (S ^⊗ₛ n).space))

end AxQM
