/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliTrotter
import AxQM.Basic.API.Evolution
import AxQM.Concrete.PauliStringBasisChange

/-!
# AxQM.Basic.API — simulating `X₁ ⊗ Y₂ ⊗ Z₃` by a single-qubit basis change

**Nielsen & Chuang, Exercise 4.51** (§4.7.3, p. 210): construct a
circuit implementing the propagator `e^{-iΔt H}` of the three-qubit Hamiltonian
`H = X₁ ⊗ Y₂ ⊗ Z₃`. This file gives the single-qubit basis change `B = H ⊗ (SH) ⊗ I` as an
`Evolution` of the three-qubit register.
-/

open Matrix NormedSpace AxQM.Concrete

noncomputable section

namespace AxQM

/-- The **basis-change gate** `B = H ⊗ (SH) ⊗ I` of Exercise 4.51, as a unitary `Evolution (qudit
(2³))` on the three-qubit register. -/
def xyzBasisChangeGate : Evolution (qudit (2 ^ 3)) where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ 3)) (kronFamilyStd basisChangeFamily)
  unitary := Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ 3)))
    (Matrix.mem_unitaryGroup_iff.mpr kronFamilyStd_basisChangeFamily_mul_conjTranspose)

end AxQM
