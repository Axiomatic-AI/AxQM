/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RegisterCompressionBridge
import AxQM.Concrete.MultiControlledSingleQubit
import AxQM.Concrete.ABCDecomposition
import AxQM.Concrete.PermutationGate
import AxQM.Concrete.ControlledSingleQubit
import AxQM.Concrete.MultiControlledNot
import AxQM.Concrete.Pauli
import AxQM.Concrete.MultiControlledNotCircuit
import AxQM.Concrete.AxisAngleGateValues
import AxQM.Concrete.DeutschWirePlacement
import AxQM.Concrete.DeutschControlledReachable
import AxQM.Concrete.EulerDecompositionOrthogonal
import Mathlib.Topology.Instances.Matrix
import AxQM.Concrete.SingleQubitWire

/-!
# Concrete: the single-qubit gates the Deutsch gate reaches on a data wire, from compressed
`G`-placements (matrix level, N&C Ex 4.44)

## The construction and results

* `deutschAncillaReachableGates fullEnc dataEnc e α` — the `G`-placement circuits that (a) preserve
  the ancilla-`|1⟩` subspace (`compressionInvariant ι`) and (b) are reachable from `G` on some three
  register wires (`closure (deutschWirePlacedReachable fullEnc a b j α)`).
-/

namespace AxQM.Concrete

open Matrix

variable {M m n D d : ℕ} (fullEnc : (Fin M → Fin 2) ≃ Fin D)
  (dataEnc : (Fin m → Fin 2) ≃ Fin d) (e : Fin M ≃ Fin m ⊕ Fin n)

/-- **The reachable, ancilla-preserving `G`-placement gate set.** A full-register matrix `N` is a
member when it (a) preserves the ancilla-`|1⟩` coordinate subspace `range (regEmbed …)`
(`compressionInvariant`), so its data-register action is well defined, and (b) is reachable from the
Deutsch gate `G = C²(iR_x(πα))` placed on some three register wires `a, b, j`
(`closure (deutschWirePlacedReachable fullEnc a b j α)`). These are the elementary `G`-placement
circuits whose compressions realise the single-qubit / reversible generators of the universality
density core. -/
noncomputable def deutschAncillaReachableGates (α : ℝ) : Set (Matrix (Fin D) (Fin D) ℂ) :=
  {N | N ∈ compressionInvariant (regEmbed fullEnc dataEnc e) ∧
    ∃ a b j : Fin M, N ∈ closure (deutschWirePlacedReachable fullEnc a b j α)}

end AxQM.Concrete
