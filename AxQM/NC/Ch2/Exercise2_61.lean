/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliMeasurement

/-!
# Nielsen & Chuang, Exercise 2.61 (measurement of `v · σ` on `|0⟩`)

*(N&C p. 90.)*

Probability of +1 for measurement of v.sigma given state |0>; post-measurement state.

* `pauliVecMeasurement` — the projective measurement of `v·σ` (its eigenprojectors `P±` as
  measurement operators), a two-outcome `Measurement (Fin 2) qubit`.
* `pauliVecMeasurement_bornProb_qubitKet0_zero` — the probability of `+1` on `|0⟩` is `(1 + v₃)/2`.
* `pauliVecMeasurement_postMeasurement_qubitKet0_zero` — the post-measurement state after `+1` is
  the normalized `P₊|0⟩` (Exercise 2.61's collapsed state).
-/

namespace AxQM

/-- The **projective measurement of the spin observable `v · σ`** on the qubit, for a real unit
vector `v` (Nielsen & Chuang §2.2.5, Exercises 2.60–2.61): the two-outcome measurement whose
operators are the eigenprojectors `P± = (I ± v·σ)/2` (outcome `0 ↔ +1`, `1 ↔ −1`). The unit-vector
hypothesis makes `(v·σ)² = I`, so the `P±` are genuine orthogonal projectors. -/
noncomputable def pauliVecMeasurement (n : Fin 3 → ℝ) (h : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    Measurement (Fin 2) qubit :=
  (pauliObservable n).signMeasurement (pauliObservable_op_mul_self h)

/-- **Nielsen & Chuang, Exercise 2.61 (probability of `+1`).** For a real unit vector `v`, the
probability of obtaining `+1` when measuring `v · σ` on the state `|0⟩` is `(1 + v₃)/2`
(here `v₃ = n 2`). -/
theorem pauliVecMeasurement_bornProb_qubitKet0_zero (n : Fin 3 → ℝ)
    (h : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    (pauliVecMeasurement n h).bornProb qubitKet0.toState 0 = (1 + n 2) / 2 := sorry

/-- **Nielsen & Chuang, Exercise 2.61 (post-measurement state).** If the `+1` outcome is obtained —
a possible outcome, `hp : p(+1) ≠ 0`, i.e. `v₃ ≠ −1` — the qubit collapses to the normalized state
`P₊|0⟩ / ‖P₊|0⟩‖`, the `+1` eigenstate of `v · σ`. -/
theorem pauliVecMeasurement_postMeasurement_qubitKet0_zero (n : Fin 3 → ℝ)
    (h : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hp : (pauliVecMeasurement n h).bornProb qubitKet0.toState 0 ≠ 0) :
    (pauliVecMeasurement n h).postMeasurement qubitKet0.toState 0 hp
      = ((pauliObservable n).postMeasPlus qubitKet0
          ((pauliObservable n).projPlus_apply_ne_zero_of_bornProb
            (pauliObservable_op_mul_self h) qubitKet0 hp)).toState := sorry

end AxQM
