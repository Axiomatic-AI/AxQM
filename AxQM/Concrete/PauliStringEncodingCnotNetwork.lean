/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringEncodingCnotLayer

/-!
# Concrete: the multi-control CNOT network of the stabilizer encoding circuit

The network of CNOT fans — one per control wire — applied by the encoding circuit of
Nielsen & Chuang **Problem 10.3** ("encoding stabilizer codes").
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-- The **multi-control CNOT network**: a CNOT fan from each control `c ∈ controls` onto its own
target list `tgt c` (`controls.flatMap (fun c => cnotFan c (tgt c))`). -/
def cnotNetwork (controls : List (Fin n)) (tgt : Fin n → List (Fin n)) : CliffordCircuit n :=
  controls.flatMap (fun c => cnotFan c (tgt c))

end AxQM.Concrete
