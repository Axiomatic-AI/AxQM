/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliGroupNegOne
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Concrete: the group-average stabilizer code projector (Nielsen & Chuang, Theorem 10.8 setup)

This file builds the **projector onto the code space `C(S)`** of a stabilizer code, directly from
the abstract stabilizer group `S`.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- The **unnormalized stabilizer sum** `Q = ∑_{s ∈ S} toMat(s)` over a stabilizer subgroup `S`. -/
noncomputable def stabilizerSum (S : Subgroup (PauliGroup n)) [Fintype S] :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ∑ s : S, (↑s : PauliGroup n).toMat

/-- The **group-average code projector** `P_S = |S|⁻¹ · ∑_{s ∈ S} toMat(s)`, the projector onto the
code space `C(S) = V_S` of the stabilizer code with stabilizer `S`. -/
noncomputable def codeProjector (S : Subgroup (PauliGroup n)) [Fintype S] :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  (Fintype.card S : ℂ)⁻¹ • stabilizerSum S

end AxQM.Concrete
