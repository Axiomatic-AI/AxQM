/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Evolution
import AxQM.Basic.API.Qubit
import AxQM.Concrete.Hadamard

/-!
# AxQM.Basic.API — the Hadamard gate as a qubit evolution

Nielsen & Chuang's Hadamard gate as a closed-system evolution of the qubit.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **Hadamard gate** `H` as a closed-system evolution of the qubit (N&C eq. 2.85). -/
def hadamardGate : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))
      Concrete.hadamardC_mem_unitaryGroup

end AxQM
