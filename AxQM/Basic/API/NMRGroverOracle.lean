/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.NMRControlledZ
import AxQM.Basic.API.ControlledRotation
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.HadamardGate
import AxQM.Concrete.HadamardRyRx
import AxQM.Basic.API.Teleportation

/-!
# AxQM.Basic.API — machinery for the NMR Grover oracles (N&C Ex 7.50)

The **two-qubit Grover search oracles** `O` and their **NMR realisations**. For a four-element
search (`n = 2` qubits) the oracle `O` for a marked item `x₀ ∈ {0,1,2,3}` flips the sign of the
basis state `|x₀⟩` and fixes every other, i.e. `O = diag` with a single `-1`. This file supplies
the `x₀ = 0, 1, 2` oracles and their circuits.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The Grover oracle for `x₀ = 0`** (`O = diag(-1,1,1,1)`). -/
def groverOracleZero : Evolution (qubit ⊗ qubit) :=
  ((pauliXGate.onLeft qubit).comp (pauliXGate.onRight qubit)).comp
    (controlledZGate.comp ((pauliXGate.onLeft qubit).comp (pauliXGate.onRight qubit)))

/-- **The Grover oracle for `x₀ = 1`** (`O = diag(1,-1,1,1)`). -/
def groverOracleOne : Evolution (qubit ⊗ qubit) :=
  (pauliXGate.onLeft qubit).comp (controlledZGate.comp (pauliXGate.onLeft qubit))

/-- **The Grover oracle for `x₀ = 2`** (`O = diag(1,1,-1,1)`). -/
def groverOracleTwo : Evolution (qubit ⊗ qubit) :=
  (pauliXGate.onRight qubit).comp (controlledZGate.comp (pauliXGate.onRight qubit))

/-- **The NMR circuit for the `x₀ = 0` oracle.** The controlled-`Z` sequence conjugated by the
physical `R_x(π)` bit-flip pulses on *both* spins — built from single-qubit rotations and the
free `J`-coupling `e^{-iH/2ℏJ}` only. -/
def nmrGroverOracleZero (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  (((rotXGate Real.pi).onLeft qubit).comp ((rotXGate Real.pi).onRight qubit)).comp
    ((nmrControlledZSequence c t).comp
      (((rotXGate Real.pi).onLeft qubit).comp ((rotXGate Real.pi).onRight qubit)))

/-- **The NMR circuit for the `x₀ = 1` oracle.** The controlled-`Z` sequence conjugated by the
physical `R_x(π)` bit-flip pulse on the first spin — single-qubit rotations and `e^{-iH/2ℏJ}`
only. -/
def nmrGroverOracleOne (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((rotXGate Real.pi).onLeft qubit).comp
    ((nmrControlledZSequence c t).comp ((rotXGate Real.pi).onLeft qubit))

/-- **The NMR circuit for the `x₀ = 2` oracle.** The controlled-`Z` sequence conjugated by the
physical `R_x(π)` bit-flip pulse on the second spin — single-qubit rotations and `e^{-iH/2ℏJ}`
only. -/
def nmrGroverOracleTwo (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((rotXGate Real.pi).onRight qubit).comp
    ((nmrControlledZSequence c t).comp ((rotXGate Real.pi).onRight qubit))

end AxQM
