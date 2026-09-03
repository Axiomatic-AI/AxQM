/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrix
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Concrete: Nielsen & Chuang Proposition 10.4 — flipping a single stabilizer generator

Nielsen & Chuang, **Proposition 10.4** (§10.5.1, p. 458): conjugation by a suitable Pauli string
flips one generator of an independent family and fixes every other.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- **Nielsen & Chuang, Proposition 10.4.** For a family of `l` phase-free generators `g₁, …, g_l`
(`g : Fin l → (Fin n → Fin 4)`) whose check-matrix rows are `ZMod 2`-linearly independent
(equivalently, by Proposition 10.3, the generators are independent; `-I ∉ S` is automatic for
phase-free Pauli strings), and any fixed index `i`, there is a Pauli string `p ∈ Gₙ` whose
conjugation **flips** `gᵢ` (`P_p P_{gᵢ} P_p† = -P_{gᵢ}`) and **fixes** every other generator
(`P_p P_{gⱼ} P_p† = P_{gⱼ}` for `j ≠ i`).
-/
theorem exists_pauliString_conj_flip {l : ℕ} (g : Fin l → (Fin n → Fin 4))
    (hindep : LinearIndependent (ZMod 2) fun j => checkRow (g j)) (i : Fin l) :
    ∃ p : Fin n → Fin 4,
      pauliString p * pauliString (g i) * star (pauliString p) = -pauliString (g i) ∧
        ∀ j, j ≠ i →
          pauliString p * pauliString (g j) * star (pauliString p) = pauliString (g j) := sorry

end AxQM.Concrete
