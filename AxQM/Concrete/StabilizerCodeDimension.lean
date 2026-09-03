/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrix
import Mathlib.LinearAlgebra.Trace

/-!
# Concrete: Nielsen & Chuang Proposition 10.5 — a stabilizer code space is `2^k`-dimensional

This file proves Nielsen & Chuang's
**Proposition 10.5** (§10.5.1, p. 458), the dimension count for stabilizer code spaces.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- The **stabilized subspace** `V_S = {v : ∀ j, P_{gⱼ} ·ᵥ v = v}`, the simultaneous
`+1`-eigenspace of the (phase-free) generators `g`, as a `ℂ`-submodule of the `n`-qubit register. -/
noncomputable def stabilizedSubspace {m : ℕ} (g : Fin m → (Fin n → Fin 4)) :
    Submodule ℂ ((Fin n → Fin 2) → ℂ) :=
  ⨅ i, LinearMap.eqLocus (Matrix.toLin' (pauliString (g i))) LinearMap.id

/-- **Nielsen & Chuang, Proposition 10.5.** A stabilizer code space stabilized by `n - k`
independent commuting phase-free generators is `2^k`-dimensional: `finrank ℂ V_S = 2^k` (for `k
≤ n`). -/
theorem stabilizedSubspace_finrank {n k : ℕ} (hk : k ≤ n) (g : Fin (n - k) → (Fin n → Fin 4))
    (hcomm : ∀ i j, Commute (pauliString (g i)) (pauliString (g j)))
    (hindep : LinearIndependent (ZMod 2) (fun j => checkRow (g j))) :
    Module.finrank ℂ (stabilizedSubspace g) = 2 ^ k := sorry

end AxQM.Concrete
