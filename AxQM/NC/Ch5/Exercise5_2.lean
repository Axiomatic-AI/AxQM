/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.QuantumFourierTransform
import AxQM.Basic.API.UniformSuperposition

/-!
# Nielsen & Chuang, Exercise 5.2 (Fourier transform of `|0…0⟩`)

*(N&C p. 217.)*

Explicitly compute the Fourier transform of the n-qubit state |00...0>.

* `qftEvolution_evolvePure_quditBasis_zero` — Exercise 5.2, for a general `d`-level register (`qudit
  (2ⁿ)` is the `n`-qubit case): `F|0⟩ = |s⟩`, i.e. `(qftEvolution d).evolvePure (quditBasis 0) =
  uniformSuperposition d`.
* `qftEvolution_evolvePure_quditBasis_zero_two_pow` — the `n`-qubit specialisation `d = 2ⁿ`, making
  the "`n`-qubit state `|00…0⟩`" of the exercise text explicit.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 5.2.** The quantum Fourier transform sends the computational-basis
ground state `|0⟩` of the register `qudit d` to the equal (uniform) superposition `N⁻¹ᐟ² ∑ₖ |k⟩`
(`N = d`):

``` F|0…0⟩ = uniformSuperposition d. ```
-/
theorem qftEvolution_evolvePure_quditBasis_zero (d : ℕ) [NeZero d] :
    (qftEvolution d).evolvePure (quditBasis (0 : Fin d)) = uniformSuperposition d := sorry

/-- **Exercise 5.2 for an `n`-qubit register** (`d = 2ⁿ`): the quantum Fourier transform of the
`n`-qubit ground state `|00…0⟩` is the equal superposition over all `2ⁿ` computational-basis
states. -/
theorem qftEvolution_evolvePure_quditBasis_zero_two_pow (n : ℕ) :
    (qftEvolution (2 ^ n)).evolvePure (quditBasis (0 : Fin (2 ^ n)))
      = uniformSuperposition (2 ^ n) := sorry

end AxQM
