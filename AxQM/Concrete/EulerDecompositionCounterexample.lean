/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochRotation
import AxQM.Concrete.RotationConjugation

/-!
# Concrete: the generalized Euler decomposition is *false* for non-parallel axes (N&C Exercise 4.11)

Nielsen & Chuang, Exercise 4.11 claims a generalized Euler decomposition along **non-parallel**
real unit vectors `m̂, n̂` for an arbitrary single-qubit unitary `U`.

## Main declarations
* `not_forall_unit_nonParallel_exists_smul_rotAxis_triple` — the **negation of Exercise 4.11**
  itself: there is no proof that every unitary decomposes as (4.13) over every non-parallel unit
  pair.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **Nielsen & Chuang, Exercise 4.11 is false as stated.** There is no proof that *every*
single-qubit unitary decomposes as `e^{iα} R_n̂(β) R_m̂(γ) R_n̂(δ)` for *every* pair of
non-parallel unit vectors `m̂, n̂`. -/
theorem not_forall_unit_nonParallel_exists_smul_rotAxis_triple :
    ¬ ∀ (m n : Fin 3 → ℝ), m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1 →
        n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 → (∀ c : ℝ, m ≠ c • n) →
      ∀ U : Matrix (Fin 2) (Fin 2) ℂ, U ∈ Matrix.unitaryGroup (Fin 2) ℂ →
        ∃ α β γ δ : ℝ,
          U = Complex.exp ((α : ℂ) * I) • (rotAxis n β * rotAxis m γ * rotAxis n δ) := sorry

end AxQM.Concrete
