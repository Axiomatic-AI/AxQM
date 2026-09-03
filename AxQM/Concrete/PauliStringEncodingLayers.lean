/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCliffordCircuit
import AxQM.Concrete.CheckMatrix

/-!
# Concrete: the Hadamard layer of the stabilizer encoding circuit

The opening **Hadamard layer** of the encoding circuit of Nielsen & Chuang **Problem 10.3**
("encoding stabilizer codes"), the circuit carrying the *trivial* check matrix `G` of Eq. (10.124)
— a listing of the single-qubit generators `Z₁, …, Zₙ` (X-part `0`, Z-part the identity) — to the
standard/encoded form of Eq. (10.125).
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-- The **pure-`Z` generator** `Zᵢ`. -/
def zGenPauli (i : Fin n) : Fin n → Fin 4 := Function.update 0 i 3

/-- The **pure-`X` generator** `Xᵢ`. -/
def xGenPauli (i : Fin n) : Fin n → Fin 4 := Function.update 0 i 1

/-- The **Hadamard layer** on the wires `ws`. Taking `ws` to be the first `r` qubits, this is the
opening layer of the stabilizer encoding circuit of Nielsen & Chuang Problem 10.3. -/
def hadLayer (ws : List (Fin n)) : CliffordCircuit n := ws.map CliffordGate.had

end AxQM.Concrete
