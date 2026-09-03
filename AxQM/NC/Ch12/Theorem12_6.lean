/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.TypicalSubspace
import AxQM.ToMathlib.Analysis.InnerProductSpace.EntanglementFidelity
import AxQM.ToMathlib.Analysis.InnerProductSpace.RankOneProjector
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumDataCompression
import AxQM.ToMathlib.InformationTheory.NoiselessCoding

/-!
# N&C Theorem 12.6 — Schumacher's noiseless channel coding theorem

*(N&C p. 544.)*

Schumacher's noiseless channel coding theorem: reliable compression iff R > S(rho).

* `ReliablyCompressible` — reliable-compressibility lifted to the primitive `State`.
* `reliablyCompressible_iff_vonNeumannEntropy_lt` — Theorem 12.6: for a non-negative
  rate `R` away from the boundary, `ρ.ReliablyCompressible R ↔ ρ.vonNeumannEntropy < R * log 2`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Reliable compressibility of a quantum source** (Nielsen & Chuang, §12.2.2), on the
primitive `State`. A source `ρ : State S` is *reliably compressible at (qubit) rate `R`*
when its density operator `ρ.op` is: there is a family of rate-`R` quantum compression schemes whose
entanglement fidelity for `ρ^⊗n` tends to `1` as the block length `n → ∞`.

The predicate's *type* names only the primitive `State`; its definition delegates to the
operator predicate on `ρ.op`. -/
def State.ReliablyCompressible (ρ : State S) (R : ℝ) : Prop :=
  ContinuousLinearMap.ReliablyCompressible ρ.op R

/-- **Schumacher's noiseless channel coding theorem** (Nielsen & Chuang, Theorem 12.6, p. 544). For
a non-negative (qubit) rate `R` away from the boundary `R = S(ρ)`, an i.i.d. quantum source `ρ` is
reliably compressible at rate `R` **iff** the rate exceeds the source entropy, `S(ρ) < R` (in nats,
`ρ.vonNeumannEntropy < R * log 2`).

This assembles N&C's two directions over the predicate `State.ReliablyCompressible`:

The hypothesis `R * log 2 ≠ ρ.vonNeumannEntropy` excludes the boundary `R = S(ρ)`, which N&C leaves
open (see the module docstring); it is the exact domain the textbook characterises, not a
weakening.
-/
theorem State.reliablyCompressible_iff_vonNeumannEntropy_lt (ρ : State S) {R : ℝ}
    (hR0 : 0 ≤ R) (hne : R * Real.log 2 ≠ ρ.vonNeumannEntropy) :
    ρ.ReliablyCompressible R ↔ ρ.vonNeumannEntropy < R * Real.log 2 := sorry

end AxQM
