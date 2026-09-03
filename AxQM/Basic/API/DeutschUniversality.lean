/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.DeutschReachableEvolutions
import AxQM.Basic.API.QuditGate
import AxQM.Basic.API.QuditTensorFactor
import AxQM.Basic.API.LeftPairGate
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.Teleportation
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle
import AxQM.Basic.API.DeutschGateMatrix
import AxQM.Concrete.DeutschRegisterBridge
import AxQM.Concrete.DeutschTensorSplit
import AxQM.Basic.API.PeriodShift
import AxQM.Concrete.MultiControlledSingleQubit
import AxQM.Concrete.SingleQubitWire
import AxQM.Concrete.DeutschCompressedReachable
import AxQM.Concrete.DeutschControlledReachable
import AxQM.Concrete.EulerDecompositionOrthogonal
import AxQM.Concrete.AxisAngleGateValues
import AxQM.Concrete.ControlledSingleQubit
import AxQM.Concrete.QFTTwoLevel
import Mathlib.LinearAlgebra.Matrix.Swap
import AxQM.Concrete.TwoLevelEmbedding
import AxQM.Concrete.ABCDecomposition
import AxQM.Concrete.PermutationGate
import AxQM.Concrete.MultiControlledNot
import AxQM.Concrete.Pauli
import AxQM.Concrete.MultiControlledNotCircuit
import AxQM.Concrete.ComplexExpUnit
import AxQM.ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM

/-!
# Universality of the Deutsch gate `G = C²(iR_x(πα))` with ancillas, at the physics level
(N&C Exercise 4.44 — the density transport + the `deutschGate α` naming)

The matrix development of Exercise 4.44 establishes universality *with ancillas* at the level of raw
matrices: for `α` irrational, the data-register actions of `G`-placement circuits with ancillas held
`|1⟩` are dense in `U(2ⁿ)` up to a global phase. Two further steps lift that to a statement about
the *physical* gate `deutschGate α`
(`= ccontrolledUnitary (iRxGate (πα))`, an `Evolution`):

## Main declarations
* `dataRegisterOp ι E` — the **data-register action** of a full-register evolution
  `E : Evolution (qudit D)`: the operator on the data space `EuclideanSpace ℂ (Fin d)` obtained by
  compressing `E`'s operator matrix to the ancilla-`|1⟩` coordinate subspace `range ι`
  (`Concrete.compress`) and re-promoting through `Matrix.toEuclideanCLM`. This is the physical
  observable of a `G`-circuit run with its ancillas held `|1⟩`.
* `exists_phase_smul_toEuclideanCLM_mem_closure_dataRegisterOp_deutschReachableEvolutions` — **the
  density transport** (`α` irrational, `≥ 1` data qubit, `≥ 2` ancillas): for any `U ∈ U(2ⁿ)` some
  global phase `e^{ia}` makes `e^{ia} • Matrix.toEuclideanCLM U` a limit of the data-register
  actions `dataRegisterOp ι '' deutschReachableEvolutions` — the physical `G`-circuits with
  ancillas are dense in the data-register unitaries up to an (unobservable) global phase.
-/

open Matrix

namespace AxQM

noncomputable section

open AxQM.Concrete

/-- **The data-register action of a full-register evolution.** For `E : Evolution (qudit D)`, the
operator on the data space obtained by compressing `E`'s operator matrix
`(Matrix.toEuclideanCLM).symm E.op` to the ancilla-`|1⟩` coordinate subspace `range ι`
(`Concrete.compress ι`) and re-promoting through `Matrix.toEuclideanCLM`. When the ancillas are held
`|1⟩` (the subspace `range ι` picks out), `dataRegisterOp ι E` is exactly the operator `E` induces
on the data register — the physical observable of the `G`-circuit `E` run with ancillas. -/
def dataRegisterOp {D d : ℕ} (ι : Fin d → Fin D) (E : Evolution (qudit D)) :
    EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)
    (compress ι ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin D)).symm E.op))

/-- **Universality of the Deutsch gate `G` with ancillas, physics level** (Nielsen & Chuang,
Exercise 4.44). When `α` is irrational, the data register has at least one qubit
(`[Nontrivial (Fin m → Fin 2)]`) and at least two ancillas (`a₀ ≠ a₁ : Fin n`), for *any* unitary
`U ∈ U(2ⁿ)` some global phase `e^{ia}` makes

  `e^{ia} • Matrix.toEuclideanCLM U
    ∈ closure (dataRegisterOp ι '' deutschReachableEvolutions fullEnc dataEnc e α)`

with `ι = Concrete.regEmbed fullEnc dataEnc e` the ancilla-`|1⟩` embedding: the data-register
actions of the register `G`-circuit evolutions `deutschReachableEvolutions` are dense in the
data-register unitaries up to an (unobservable) global phase.
-/
theorem exists_phase_smul_toEuclideanCLM_mem_closure_dataRegisterOp_deutschReachableEvolutions
    {M m n D d : ℕ} (fullEnc : (Fin M → Fin 2) ≃ Fin D)
    (dataEnc : (Fin m → Fin 2) ≃ Fin d) (e : Fin M ≃ Fin m ⊕ Fin n)
    [Nontrivial (Fin m → Fin 2)] {α : ℝ} (hα : Irrational α) (a₀ a₁ : Fin n) (ha : a₀ ≠ a₁)
    {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ a : ℝ,
      Complex.exp ((a : ℂ) * Complex.I) • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) U ∈
        closure (dataRegisterOp (regEmbed fullEnc dataEnc e) ''
          (deutschReachableEvolutions fullEnc dataEnc e α : Set (Evolution (qudit D)))) := sorry

end

end AxQM
