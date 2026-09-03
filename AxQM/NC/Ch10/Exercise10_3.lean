/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BitFlipSyndromeMeasurement

/-!
# Nielsen & Chuang, Exercise 10.3 — the bit-flip syndrome measured two ways

*(N&C p. 430.)*

Measuring Z1Z2 then Z2Z3 equals measuring the four bit-flip projectors, same statistics and
post-states.

* `bitFlipSyndrome_bornProb_eq` — same statistics: for every state `ρ` and joint outcome `s`, the
  cascade's Born probability for `s` equals the four-projector measurement's Born probability for
  the relabeled outcome `bitFlipRelabel s`.
* `bitFlipSyndrome_postMeasurement_eq` — same post-measurement states: whenever the joint outcome
  `s` is possible, the two procedures collapse `ρ` to the *same* state.
-/

noncomputable section

namespace AxQM

/-- **Exercise 10.3 — same measurement statistics.** Measuring `Z₁Z₂` then `Z₂Z₃` (the cascade
`bitFlipZ12Measurement.cascade bitFlipZ23Measurement`) assigns to the joint outcome `s : Fin 2 ×
Fin 2` exactly the Born probability that measuring the four syndrome projectors
(`bitFlipSyndromeMeasurement`) assigns to the relabeled outcome `bitFlipRelabel s`, for every
state `ρ`. -/
theorem bitFlipSyndrome_bornProb_eq (ρ : State bitFlipReg) (s : Fin 2 × Fin 2) :
    (bitFlipZ12Measurement.cascade bitFlipZ23Measurement).bornProb ρ s
      = bitFlipSyndromeMeasurement.bornProb ρ (bitFlipRelabel s) :=
  Measurement.bornProb_congr (cascade_op_eq_syndromeProj s) ρ

/-- **Exercise 10.3 — same post-measurement states.** Whenever the joint outcome `s` of measuring
`Z₁Z₂` then `Z₂Z₃` is possible, the collapsed state equals the collapsed state of
measuring the four syndrome projectors for the relabeled outcome `bitFlipRelabel s`: the two
procedures update `ρ` identically. -/
theorem bitFlipSyndrome_postMeasurement_eq (ρ : State bitFlipReg) (s : Fin 2 × Fin 2)
    (hs : (bitFlipZ12Measurement.cascade bitFlipZ23Measurement).bornProb ρ s ≠ 0) :
    (bitFlipZ12Measurement.cascade bitFlipZ23Measurement).postMeasurement ρ s hs
      = bitFlipSyndromeMeasurement.postMeasurement ρ (bitFlipRelabel s)
          (by rw [← bitFlipSyndrome_bornProb_eq]; exact hs) := sorry

end AxQM
