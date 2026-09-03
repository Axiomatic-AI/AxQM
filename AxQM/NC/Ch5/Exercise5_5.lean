/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.InverseQuantumFourierTransform

/-!
# Nielsen & Chuang, Exercise 5.5 — a quantum circuit for the inverse quantum Fourier transform

*(N&C p. 221.)*

Give a quantum circuit to perform the inverse quantum Fourier transform.

* `qftInverseEvolution_evolvePure_quditBasis` — the inverse discrete Fourier transform: `F⁻¹|k⟩ = ∑ⱼ
  (1/√d)·e^{−2πijk/d} |j⟩`, the conjugate of the forward action (5.2), confirming the circuit
  performs the *inverse* transform.
* `qftInverseEvolution_comp_qftEvolution` — `F⁻¹ ∘ F = id`: the inverse circuit undoes the QFT
  circuit, as a *gate identity*.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 5.5 — the inverse discrete Fourier transform.** The inverse QFT
circuit sends the computational-basis state `|k⟩` of the register `qudit d` to the inverse-Fourier
superposition `∑ⱼ (1/√d)·e^{−2πijk/d} |j⟩`:
`evolvePure F⁻¹ |k⟩ = qftInverseFourierImage d k`.

The amplitudes are the conjugates of the forward QFT amplitudes (5.2), the defining sign flip of the
inverse transform. -/
theorem qftInverseEvolution_evolvePure_quditBasis (d : ℕ) [NeZero d] (k : Fin d) :
    (qftInverseEvolution d).evolvePure (quditBasis k) = qftInverseFourierImage d k := sorry

/-- **Nielsen & Chuang, Exercise 5.5 — the inverse circuit undoes the QFT circuit** (gate identity):
`F⁻¹ ∘ F = id`. Applying the QFT circuit and then the inverse-QFT circuit is the identity gate. -/
theorem qftInverseEvolution_comp_qftEvolution (d : ℕ) [NeZero d] :
    (qftInverseEvolution d).comp (qftEvolution d) = Evolution.id := sorry

end AxQM
