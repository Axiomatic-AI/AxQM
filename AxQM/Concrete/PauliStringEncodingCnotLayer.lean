/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringEncodingLayers

/-!
# Concrete: the CNOT layer of the stabilizer encoding circuit

The **fan of CNOTs from one control**, the repeated unit of the CNOT layer in Nielsen & Chuang's
encoding circuit for a stabilizer code in standard form (**Problem 10.3**, eq. (10.125)).
-/

open Matrix

noncomputable section

namespace AxQM.Concrete

variable {n : ℕ}

/-- A **single CNOT step** from control `i` to target `t`: the one-gate circuit `[CNOT_{i→t}]`,
or the empty circuit if `t = i` (a self-target is skipped). This keeps the CNOT fan total. -/
def cnotStep (i t : Fin n) : CliffordCircuit n :=
  if h : i = t then [] else [CliffordGate.cnot i t h]

/-- The **CNOT fan** from control wire `i` onto the target wires `ts`. -/
def cnotFan (i : Fin n) (ts : List (Fin n)) : CliffordCircuit n := ts.flatMap (cnotStep i)

end AxQM.Concrete

end
