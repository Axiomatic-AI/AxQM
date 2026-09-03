/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BellLocalMeasurement

/-!
# Nielsen & Chuang, Exercise 12.32 — local `Z` measurements reproduce the `Π_bf` statistics

*(N&C p. 595.)*

Local X,Z measurements give same statistics as Bell-basis projectors Pi_bf,Pi_pf.

* `localZParity_bornProb_eq_bitFlipMeasurement`
* `localXParity_bornProb_eq_phaseFlipMeasurement`
-/

noncomputable section

namespace AxQM

/-- **Exercise 12.32 (bit-flip half).** The statistics Alice and Bob compile from their **local**
`Z` measurements — the parity `zParity` of the two outcomes, coarse-grained from
`localZMeasurement` — are, for *every* state `ρ`, identical to those of the Bell-basis `Π_bf`
measurement (`bellMeasurement.coarseGrain bitFlipIndex`). -/
theorem localZParity_bornProb_eq_bitFlipMeasurement (ρ : State (qubit ⊗ qubit)) (k : Fin 2) :
    (localZMeasurement.coarseGrain zParity).bornProb ρ k
      = (bellMeasurement.coarseGrain bitFlipIndex).bornProb ρ k := sorry

/-- **Exercise 12.32 (phase-flip half).** The statistics Alice and Bob compile from their **local**
`X` measurements — the parity `xParity` of the two outcomes, coarse-grained from
`localXMeasurement` — are, for *every* state `ρ`, identical to those of the Bell-basis `Π_pf`
measurement (`bellMeasurement.coarseGrain phaseFlipIndex`). -/
theorem localXParity_bornProb_eq_phaseFlipMeasurement (ρ : State (qubit ⊗ qubit)) (k : Fin 2) :
    (localXMeasurement.coarseGrain xParity).bornProb ρ k
      = (bellMeasurement.coarseGrain phaseFlipIndex).bornProb ρ k := sorry

end AxQM
