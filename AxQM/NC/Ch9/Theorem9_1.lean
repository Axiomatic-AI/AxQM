/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.TraceDistance
import AxQM.Basic.Measurement
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
import AxQM.Concrete.ClassicalTraceDistance

/-!
# Nielsen & Chuang, Theorem 9.1 (trace distance as the maximum over measurements)

*(N&C p. 405.)*

D(rho,sigma) = max over POVMs of classical D(p_m,q_m) of measurement outcomes.

* `isGreatest_classicalTraceDist_bornProb` — `D(ρ, σ)` is the *greatest*
  achievable classical trace distance — the two directions assembled into N&C's
  equality-to-a-maximum via `IsGreatest`.
-/

open scoped InnerProductSpace
open AxQM.Concrete

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Theorem 9.1**: the trace distance `D(ρ, σ)` is the **greatest**
classical trace distance of the outcome distributions achievable over all measurements — `D(ρ,
σ) = max_{measurements} D(pₘ, qₘ)`.

The equality-to-a-maximum is packaged as `IsGreatest`. The measurements
range over every finite outcome cardinality `Fin n`; since every POVM is the induced POVM of
some measurement, this is N&C's maximum over all POVMs.
-/
theorem State.isGreatest_classicalTraceDist_bornProb (ρ σ : State S) :
    IsGreatest
      {d : ℝ | ∃ (n : ℕ) (m : Measurement (Fin n) S),
        d = classicalTraceDist (m.bornProb ρ) (m.bornProb σ)}
      (ρ.traceDistance σ) := sorry

end AxQM
