/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringEncodingCnotLayer

/-!
# Concrete: the phase / controlled-`Z` gates of the stabilizer encoding circuit

The phase (`S`) layer and the controlled-`Z` gate used by the encoding circuit of Nielsen &
Chuang, Problem 10.3 ("encoding stabilizer codes"), §10.5.
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-- The **phase layer** on the wires `ws`. -/
def sLayer (ws : List (Fin n)) : CliffordCircuit n := ws.map CliffordGate.phase

/-- The **controlled-`Z` gate** between control wire `c` and target wire `t` (`h : c ≠ t`), realized
in the elementary gate set `{H, S, CNOT}` as `CZ_{c,t} = H_t · CNOT_{c→t} · H_t` — the
three-gate Clifford circuit `[had t, cnot c t, had t]` (the head `had t` is applied last). -/
def czGate (c t : Fin n) (h : c ≠ t) : CliffordCircuit n :=
  [CliffordGate.had t, CliffordGate.cnot c t h, CliffordGate.had t]

end AxQM.Concrete
