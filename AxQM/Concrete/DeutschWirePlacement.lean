/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DeutschControlledReachable
import AxQM.Concrete.MultiControlledSingleQubit

/-!
# Concrete: the Deutsch gate placed on register wires (matrix level, N&C Ex 4.44)
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **The placed reachable set of the Deutsch gate.** The Deutsch iterates `{mcCtrlSingleQubit enc
{a, b} j (iⁿ R_x(nπα))}` placed with controls `a, b` and target `j`. -/
noncomputable def deutschWirePlacedReachable (enc : (Fin m → Fin 2) ≃ Fin d) (a b j : Fin m)
    (α : ℝ) : Set (Matrix (Fin d) (Fin d) ℂ) :=
  mcCtrlSingleQubit enc {a, b} j '' deutschTargetOrbit α

end AxQM.Concrete
