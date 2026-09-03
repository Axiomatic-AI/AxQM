/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.TraceDistance
import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Strictly contractive state-maps and uniqueness of fixed points (Nielsen & Chuang §9.2.1)

Strict contraction for a trace-preserving quantum operation `E`, as used in the fixed-point
exercises of Nielsen & Chuang §9.2.1 (Exercises 9.9–9.13, p. 408–409).

## Main declarations

* `AxQM.StrictlyContractive` — the predicate `∀ ρ σ, ρ ≠ σ → D(f ρ, f σ) < D(ρ, σ)`.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information* (10th anniv.
ed.). Cambridge University Press. §9.2.1, Exercises 9.9–9.13 (p. 408–409).
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- A state-map `f : State S → State S` is **strictly contractive** for the trace distance when it
strictly decreases the distance between any two *distinct* states:
`D(f ρ, f σ) < D(ρ, σ)` whenever `ρ ≠ σ`.

This is the metric notion of a *contractive* map (Edelstein): unlike `ContractingWith K`, it assumes
no uniform contraction constant `K < 1`. The `ρ ≠ σ` guard is the honest reading of N&C's informal
"for any `ρ` and `σ`" — at `ρ = σ` the strict inequality is impossible, so an unguarded quantifier
would be a `False` hypothesis. -/
def StrictlyContractive (f : State S → State S) : Prop :=
  ∀ ρ σ : State S, ρ ≠ σ → (f ρ).traceDistance (f σ) < ρ.traceDistance σ

end AxQM
