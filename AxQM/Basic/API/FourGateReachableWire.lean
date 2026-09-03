/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuditGate
import AxQM.Basic.API.HadamardGate
import AxQM.Concrete.QftGateCircuit
import AxQM.Basic.API.PiEighthGate
import AxQM.Basic.API.HadamardRotation
import AxQM.Concrete.Rotation
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# The reachable single-qubit rotations on a register wire (N&C Exercise 4.43, four-gate bridge —
register-lift stage, register-side ingredients)

## Main declarations
* `rotZWireEvolution n t θ` — the rotation `R_z(θ)` placed on wire `t` of the `2ⁿ`-level register,
  as a named `Evolution (qudit (2ⁿ))`: the `quditGate` promotion of the gate matrix
  `singleQubitOnWire finFunctionFinEquiv t (rotZ θ)`.
-/

open Matrix

namespace AxQM

noncomputable section

open AxQM.Concrete

/-- **The reachable `z`-rotation on a register wire.** The rotation `R_z(θ)` placed on wire `t` of
the `2ⁿ`-level register, as a named `Evolution (qudit (2ⁿ))`. -/
def rotZWireEvolution (n : ℕ) (t : Fin n) (θ : ℝ) : Evolution (qudit (2 ^ n)) :=
  quditGate (singleQubitOnWire_mem_unitaryGroup finFunctionFinEquiv t (rotZ_mem_unitaryGroup θ))

end

end AxQM
