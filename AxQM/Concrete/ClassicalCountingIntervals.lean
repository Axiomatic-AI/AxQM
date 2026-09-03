/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Tactic

/-!
# Concrete: the solution count for the classical counting query lower bound

Shared infrastructure for the classical query lower bound of Nielsen & Chuang §6.3: any classical
counting algorithm must make `Ω(N)` oracle calls.
-/

namespace AxQM.Concrete

variable {N : ℕ}

/-- The **number of solutions** of a Boolean oracle `f : Fin N → Bool`: the number of indices at
which `f` is `true`. For the counting problem this is the quantity `M` an algorithm estimates. -/
def numSolutions (f : Fin N → Bool) : ℕ := (Finset.univ.filter fun x => f x = true).card

end AxQM.Concrete
