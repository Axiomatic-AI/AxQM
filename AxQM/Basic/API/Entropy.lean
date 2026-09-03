/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.StateSpace
import AxQM.Basic.SystemIso
import AxQM.ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropy

/-!
# AxQM — von Neumann entropy of a quantum state

The **von Neumann entropy** of a quantum state `ρ` (Nielsen–Chuang §11.3.1, eq. (11.44)) is
`S(ρ) = −tr(ρ log ρ)`.

## Main definitions

* `AxQM.State.vonNeumannEntropy` — the von Neumann entropy `S(ρ)` of a state `ρ`.

## Main results

* `AxQM.State.vonNeumannEntropy_nonneg` — `S(ρ) ≥ 0`.
* `AxQM.State.vonNeumannEntropy_le_log_finrank` — `S(ρ) ≤ log d`, `d = dim S.space`.
-/

namespace AxQM

variable {S : QSystem}

/-- The **von Neumann entropy** `S(ρ) = -tr(ρ log ρ)` of a quantum state `ρ`
(Nielsen–Chuang §11.3.1, eq. (11.44)): the Shannon entropy of the eigenvalue spectrum of the
density operator `ρ.op`. -/
noncomputable def State.vonNeumannEntropy (ρ : State S) : ℝ :=
  ρ.op.vonNeumannEntropy

/-- **Non-negativity of the von Neumann entropy** (Nielsen–Chuang Theorem 11.8, first item):
`S(ρ) ≥ 0`. -/
theorem State.vonNeumannEntropy_nonneg (ρ : State S) : 0 ≤ ρ.vonNeumannEntropy := sorry

/-- **Upper bound on the von Neumann entropy** (Nielsen–Chuang Theorem 11.8, second item): `S(ρ) ≤
log d` where `d = dim S.space`, with equality for the maximally mixed state. -/
theorem State.vonNeumannEntropy_le_log_finrank (ρ : State S) :
    ρ.vonNeumannEntropy ≤ Real.log (Module.finrank ℂ S.space : ℝ) := sorry

end AxQM
