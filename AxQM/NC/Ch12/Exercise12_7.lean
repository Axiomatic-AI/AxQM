/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ArakiLiebEqualityConditions
import AxQM.Basic.API.ControlledControlledUnitary
import Mathlib.Analysis.InnerProductSpace.PiL2
import AxQM.NC.Ch12.Theorem12_6
import AxQM.ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Nielsen & Chuang, Exercise 12.7 — the qubit data-compression source `ρ = p|0⟩⟨0| + (1−p)|1⟩⟨1|`

*(N&C p. 546.)*

Outline circuit to compress qubit source rho = p|0><0|+(1-p)|1><1| into nR qubits.

* `qubitClassicalSource` — the source `ρ(p) = p|0⟩⟨0| + (1−p)|1⟩⟨1|`, as the mixture (`State.mix`)
  of the computational pure states `|0⟩, |1⟩` with weights `p, 1 − p`.
* `qubitClassicalSource_vonNeumannEntropy` — `S(ρ) = H(p)`: the von Neumann entropy of the source
  equals the binary Shannon entropy of the mixing weights.
* `qubitClassicalSource_reliablyCompressible` — the achievability claim: for every rate with
  `H(p) < R · log 2` (i.e. `R > H(p)`), the source is reliably compressible at rate `R`.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

/-- **The qubit data-compression source of N&C Exercise 12.7:** `ρ(p) = p|0⟩⟨0| + (1 − p)|1⟩⟨1|`,
the i.i.d. qubit source whose two computational levels `|0⟩, |1⟩` carry probabilities `p`, `1 −
p`. -/
def qubitClassicalSource (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : State qubit :=
  State.mix ![p, 1 - p]
    (Fin.forall_fin_two.mpr ⟨hp0, by change (0 : ℝ) ≤ 1 - p; linarith⟩)
    (by rw [Fin.sum_univ_two]; change p + (1 - p) = 1; ring)
    (fun i => (qubitBasis i).toState)

/-- **N&C Exercise 12.7, the entropy identity `S(ρ) = H(p)`.** For the source `ρ(p) = p|0⟩⟨0| + (1 −
p)|1⟩⟨1|`, the von Neumann entropy equals the binary Shannon entropy `H(p) = Real.entropy ![p, 1
− p]` of the mixing weights. -/
theorem qubitClassicalSource_vonNeumannEntropy (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (qubitClassicalSource p hp0 hp1).vonNeumannEntropy = Real.entropy ![p, 1 - p] := sorry

/-- **N&C Exercise 12.7, the achievability claim.** The source `ρ(p) = p|0⟩⟨0| + (1 − p)|1⟩⟨1|` is
**reliably compressible at every rate `R > H(p)`** — the exercise's compression into `nR` qubits
for any `R > S(ρ) = H(p)`. -/
theorem qubitClassicalSource_reliablyCompressible (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R : ℝ}
    (hR : Real.entropy ![p, 1 - p] < R * Real.log 2) :
    (qubitClassicalSource p hp0 hp1).ReliablyCompressible R := sorry

end AxQM
