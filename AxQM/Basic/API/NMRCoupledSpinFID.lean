/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution
import AxQM.ToMathlib.Analysis.Normed.Algebra.ExponentialInvolution
import AxQM.Basic.API.Observable
import AxQM.Basic.API.Qubit

/-!
# AxQM.Basic.API — the J-coupled NMR readout operator (Nielsen & Chuang §7.7)

The two-spin `J`-coupling Hamiltonian and the **transverse magnetization readout operator** of an
NMR system (Nielsen & Chuang §7.7, Exercise 7.37).
-/

open scoped ComplexOrder

noncomputable section

namespace AxQM

variable (J : ℝ)

/-- The **two-spin `J`-coupling Hamiltonian** `H = J Z₁Z₂` of Nielsen & Chuang §7.7, as an
`Observable` on the two-qubit system whose operator is `J • (Z ⊗ Z)` — a real scalar multiple of
the `Z ⊗ Z` observable, the NMR Ising/`ZZ` coupling between two spins with coupling constant `J`. -/
def couplingZZHamiltonian : Observable (qubit.compose qubit) where
  op := (J : ℂ) • (pauliZObservable.tmul pauliZObservable).op
  selfAdjoint :=
    ((Complex.im_eq_zero_iff_isSelfAdjoint _).mp rfl).smul
      (pauliZObservable.tmul pauliZObservable).selfAdjoint

/-- The **spin-1 transverse magnetization readout** operator `i X₁ + Y₁` (`X₁ = X ⊗ 1`,
`Y₁ = Y ⊗ 1`) — the `k = 1` case of the non-Hermitian pickup operator `i Xₖ + Yₖ` of the
free-induction-decay signal `V(t)` (Nielsen & Chuang eq. 7.143). -/
def nmrTransverseReadout : (qubit.compose qubit).space →L[ℂ] (qubit.compose qubit).space :=
  Complex.I • (pauliXObservable.tmul (Observable.id qubit)).op
    + (pauliYObservable.tmul (Observable.id qubit)).op

end AxQM
