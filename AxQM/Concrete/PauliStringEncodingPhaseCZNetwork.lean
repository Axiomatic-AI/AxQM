/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringEncodingPhaseCZLayer

/-!
# Concrete: the phase / controlled-`Z` network of the encoding circuit

The `Z`-depositing layer of the stabilizer encoding circuit of Nielsen & Chuang **Problem 10.3**
("encoding stabilizer codes"): a phase gate on each pivot wire carrying a diagonal `B`-entry, and a
controlled-`Z` on each pair of wires carrying an off-diagonal `B`- or a `C₂`-entry of the standard
form (10.125).
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-- A **single controlled-`Z` step** on the pair `(c, t)`: the three-gate circuit `czGate c t`, or
the empty circuit if `c = t` (a self-pair is skipped). -/
def czStep (c t : Fin n) : CliffordCircuit n :=
  if h : c = t then [] else czGate c t h

/-- The **controlled-`Z` network**: a `CZ` on each pair `(c, t) ∈ pairs` (`pairs.flatMap (fun p =>
czStep p.1 p.2)`). -/
def czNetwork (pairs : List (Fin n × Fin n)) : CliffordCircuit n :=
  pairs.flatMap (fun p => czStep p.1 p.2)

/-- The **phase / controlled-`Z` network** of the stabilizer encoding circuit:
the phase layer on the wires `ws` (the diagonal of `B`) followed by the controlled-`Z` network on
`pairs` (the off-diagonal `B` and the block `C₂`), `sLayer ws ++ czNetwork pairs`. -/
def phaseCZNetwork (ws : List (Fin n)) (pairs : List (Fin n × Fin n)) : CliffordCircuit n :=
  sLayer ws ++ czNetwork pairs

end AxQM.Concrete
