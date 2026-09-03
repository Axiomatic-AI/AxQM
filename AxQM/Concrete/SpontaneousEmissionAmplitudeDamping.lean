/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.JaynesCummingsUnitary
import AxQM.Concrete.AmplitudeDampingChannel
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# Concrete: spontaneous emission is amplitude damping (N&C Exercise 8.24)

It works, at the level of raw
operators on an arbitrary two-dimensional complex inner product space `H` (a qubit) with a chosen
computational orthonormal basis `b : OrthonormalBasis (Fin 2) ℂ H`, through Nielsen & Chuang,
*Quantum Computation and Quantum Information*, **Exercise 8.24** (p. 381–382): *spontaneous emission
is amplitude damping*. Take the resonant Jaynes–Cummings (vacuum-Rabi) unitary `U`
(`Concrete.jaynesCummingsZeroDetuningUnitary`, N&C eq. 7.77 at detuning `δ = 0`)
on `H ⊗[ℂ] H` — the **atom** (left factor) coupled to a
single field **mode** (right factor) — and give the quantum operation obtained by *tracing over the
field*.

## Contents

* `spontaneousEmissionDilation b g t = U (· ⊗ |0⟩_field)` — the dilation `V`.
* `spontaneousEmissionChannel b g t ρ = tr_field(V ρ V†)`, with **the answer**
  `spontaneousEmissionChannel_eq_ampDampChannel : spontaneousEmissionChannel b g t ρ =
  ampDampChannel b (sin²(gt)) ρ` (for `0 ≤ cos(gt)`).
-/

open scoped TensorProduct InnerProductSpace

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The **dilation** `V = U (· ⊗ |0⟩_field) : H →ₗ H ⊗ H`: prepare the field in the vacuum `|0⟩`,
then apply the resonant Jaynes–Cummings (vacuum-Rabi) unitary. Its operation elements
`krausOp b V k` are the Kraus operators of the spontaneous-emission channel. -/
noncomputable def spontaneousEmissionDilation (g t : ℝ) : H →ₗ[ℂ] H ⊗[ℂ] H :=
  jaynesCummingsZeroDetuningUnitary b g t ∘ₗ LinearMap.embedRight b 0

/-- The **spontaneous-emission quantum operation**, in dilation form `E(ρ) = tr_field(V ρ V†)` (the
operator-sum route to `tr_field(U (ρ ⊗ |0⟩⟨0|) U†)`). -/
noncomputable def spontaneousEmissionChannel (g t : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  LinearMap.partialTraceRight b (spontaneousEmissionDilation b g t ∘ₗ ρ ∘ₗ
    LinearMap.adjoint (spontaneousEmissionDilation b g t))

omit [CompleteSpace H] in
/-- **N&C Exercise 8.24 (the answer): spontaneous emission is amplitude damping.** Tracing the field
out of the resonant Jaynes–Cummings evolution returns exactly the amplitude-damping channel
`E_AD` at `γ = sin²(gt)`:

`tr_field(U (ρ ⊗ |0⟩⟨0|) U†) = E_AD(ρ)`,   for `0 ≤ cos(gt)`.
-/
theorem spontaneousEmissionChannel_eq_ampDampChannel (g t : ℝ) (hcos : 0 ≤ Real.cos (g * t))
    (ρ : H →ₗ[ℂ] H) :
    spontaneousEmissionChannel b g t ρ = ampDampChannel b (Real.sin (g * t) ^ 2) ρ := sorry

end AxQM.Concrete

end
