/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.NMRCoupledSpinFID
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.ContinuousSearchHamiltonian
import AxQM.Basic.API.ControlledUnitary
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.PiEighthGate
import AxQM.Basic.API.HadamardRotation

/-!
# AxQM.Basic.API — machinery for the NMR controlled-`Z` (N&C Ex 7.41)

The **controlled-`Z` gate** realised from the two-spin NMR Hamiltonian (N&C eq. 7.147,
`Hsys = a Z₁ + b Z₂ + c Z₁Z₂`) by one period of `Z₁Z₂`-coupled evolution and a few single-qubit
`z`-rotations.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The global-phase gate** `e^{iα} · 1` as an `Evolution` on a quantum system `S`: the unitary
that multiplies every state vector by the fixed unit-modulus scalar `e^{iα}`. It reifies the
scalar prefactor `√i = e^{iπ/4}` appearing in N&C's controlled-`Z` construction (eq. 7.152). -/
def globalPhaseGate (α : ℝ) : Evolution S where
  op := Complex.exp ((α : ℂ) * Complex.I) • (1 : S.space →L[ℂ] S.space)
  unitary := by
    rw [Unitary.mem_iff]
    have hconj : (starRingEnd ℂ) (Complex.exp ((α : ℂ) * Complex.I))
        = Complex.exp (-((α : ℂ) * Complex.I)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp [Complex.conj_I, mul_comm]
    have hmul : (starRingEnd ℂ) (Complex.exp ((α : ℂ) * Complex.I))
        * Complex.exp ((α : ℂ) * Complex.I) = 1 := by
      rw [hconj, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have hmul' : Complex.exp ((α : ℂ) * Complex.I)
        * (starRingEnd ℂ) (Complex.exp ((α : ℂ) * Complex.I)) = 1 := by
      rw [mul_comm]; exact hmul
    constructor
    · rw [star_smul, star_one, smul_mul_smul_comm, one_mul, ← starRingEnd_apply, hmul, one_smul]
    · rw [star_smul, star_one, smul_mul_smul_comm, one_mul, ← starRingEnd_apply, hmul', one_smul]

/-- **The NMR controlled-`Z` gate sequence**: one period of evolution under the `Z₁Z₂` coupling
`(couplingZZHamiltonian c).propagator 1 0 t = exp(-i c Z₁Z₂ t)`, followed by a `90°` `z`-rotation
`R_z(-π/2)` on each of the two spins. -/
def nmrControlledZSequence (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((couplingZZHamiltonian c).propagator 1 0 t).comp
    (((rotZGate (-(Real.pi / 2))).onLeft qubit).comp
      ((rotZGate (-(Real.pi / 2))).onRight qubit))

end AxQM
