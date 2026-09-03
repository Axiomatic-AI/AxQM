/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuantumFourierTransform
import AxQM.Basic.API.InverseQuantumFourierTransform
import AxQM.Basic.API.Qudit
import AxQM.Basic.API.Evolution

/-!
# Nielsen & Chuang, Problem 5.6 (Addition by Fourier transforms)

*(N&C p. 244.)*

Addition by Fourier transforms: circuit for |x> -> |x+y mod 2^n> via QFT, phase shifts, inverse QFT.

* `fourierAddPhase`
* `additionByFourier`
* `additionByFourier_evolvePure_quditBasis` — correctness: `A_y |x⟩ = |x+y mod d⟩`.
-/

noncomputable section

namespace AxQM

/-- The **Fourier-basis phase-shift layer** `D_y` of Nielsen & Chuang Problem 5.6, on the register
`qudit d`: the diagonal gate imprinting the phase `e^{2πi yk/d}` on the `k`-th Fourier mode,
`D_y|k⟩ = e^{2πi yk/d}|k⟩`. Modelled as `diagPhase` with the angle `θ_k = 2π y k / d` (so
`e^{iθ_k} = e^{2πi yk/d}`). -/
def fourierAddPhase (d : ℕ) (y : Fin d) : Evolution (qudit d) :=
  diagPhase (fun k => 2 * Real.pi * (y : ℕ) * (k : ℕ) / d)

/-- The **Fourier-addition circuit** `A_y = F⁻¹ ∘ D_y ∘ F` of Nielsen & Chuang Problem 5.6, on the
register `qudit d`: the quantum Fourier transform `F` (`qftEvolution d`), then the single-qubit
phase-shift layer `D_y` (`fourierAddPhase d y`), then the inverse Fourier transform `F⁻¹`
(`qftInverseEvolution d`). -/
def additionByFourier (d : ℕ) [NeZero d] (y : Fin d) : Evolution (qudit d) :=
  (qftInverseEvolution d).comp ((fourierAddPhase d y).comp (qftEvolution d))

/-- **Nielsen & Chuang, Problem 5.6 (correctness):** the Fourier-addition circuit `A_y = F⁻¹ ∘ D_y ∘
F` computes constant addition `|x⟩ ↦ |x+y mod d⟩`: `(additionByFourier d y).evolvePure |x⟩ =
|x+y⟩` (with `+` the modular addition of `Fin d`). -/
theorem additionByFourier_evolvePure_quditBasis (d : ℕ) [NeZero d] (x y : Fin d) :
    (additionByFourier d y).evolvePure (quditBasis x) = quditBasis (x + y) := sorry

end AxQM
