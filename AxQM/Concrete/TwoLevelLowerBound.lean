/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QFTTwoLevel
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Concrete: a `d × d` unitary needing `≥ d − 1` two-level factors (N&C Ex 4.38)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.38 (p. 191).
-/

namespace AxQM.Concrete

open Matrix Module

variable {d : ℕ}

/-- The `i`-th standard basis vector of `Fin d → ℂ` (value `1` at `i`, `0` elsewhere). -/
def stdVec (i : Fin d) : Fin d → ℂ := Pi.single i 1

/-- The standard basis vectors of `Fin d → ℂ` are self-conjugate: `star (stdVec i) = stdVec i`. -/
lemma star_stdVec (i : Fin d) : star (stdVec i) = stdVec i := by
  rw [stdVec, Pi.star_single, star_one]

/-- **Nielsen & Chuang, Exercise 4.38.** For every `d`, there is a `d × d` unitary matrix that
cannot be written as a product of fewer than `d − 1` two-level unitary matrices: any list of
two-level unitaries whose product equals it has length at least `d − 1`. -/
theorem exists_unitary_two_level_decomposition_length_ge (d : ℕ) :
    ∃ U ∈ Matrix.unitaryGroup (Fin d) ℂ,
      ∀ L : List (Matrix (Fin d) (Fin d) ℂ),
        (∀ V ∈ L, IsTwoLevelUnitary V) → L.prod = U → d - 1 ≤ L.length := sorry

end AxQM.Concrete
