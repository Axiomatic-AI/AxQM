/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.StrictContraction
import AxQM.NC.Ch9.Exercise9_9

/-!
# Nielsen & Chuang, Exercise 9.10 (Unique fixed point of a strictly contractive operation)

*(N&C p. 408.)*

Show a strictly contractive trace-preserving quantum op has a unique fixed point.

* `existsUnique_fixedPoint_of_strictlyContractive` — the full Exercise 9.10: a strictly contractive
  trace-preserving quantum operation (`IsChannel` and `StrictlyContractive`) of a genuine quantum
  system has a *unique* fixed point, `∃! ρ, E(ρ) = ρ`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.10 (unique fixed point of a strictly contractive operation).** A
*strictly contractive trace-preserving quantum operation* `f` — one that is both a channel
(`IsChannel`) and strictly contractive (`StrictlyContractive`) — of a genuine quantum system has
a **unique** fixed point: `∃! ρ, f ρ = ρ`.

The instance `[Nonempty (State S)]` records that `S` is a genuine quantum system (its state space
is nonzero-dimensional); without it, "a fixed state exists" is vacuously false.
-/
theorem IsChannel.existsUnique_fixedPoint_of_strictlyContractive [Nonempty (State S)]
    {f : State S → State S} (hchan : IsChannel f) (hf : StrictlyContractive f) :
    ∃! ρ : State S, f ρ = ρ := sorry

end AxQM
