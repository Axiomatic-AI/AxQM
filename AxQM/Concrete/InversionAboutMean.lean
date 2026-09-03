/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Concrete: the inversion-about-the-mean operator (Nielsen & Chuang, Exercise 6.2)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 6.2 (p. 251)
asks to show that the operator `2|ψ⟩⟨ψ| − I` — the second half of the Grover iteration,
`H⊗ⁿ (2|0⟩⟨0| − I) H⊗ⁿ = 2|ψ⟩⟨ψ| − I` (Eq. 6.6) — applied to a general state
`∑ₖ αₖ|k⟩` produces `∑ₖ (−αₖ + 2⟨α⟩)|k⟩` (Eq. 6.7), where `|ψ⟩ = (1/√N) ∑ₓ|x⟩` is the
equally-weighted superposition (6.4) and `⟨α⟩ ≡ (∑ₖ αₖ)/N` is the mean of the amplitudes.
Because the amplitude of each `|k⟩` is reflected through the common mean `⟨α⟩`, this
operator is N&C's *inversion about the mean*.

## Contents

* `reflectionMatrix u` — the general reflection / "`2P − I`" operator `2|u⟩⟨u| − I`
  built from the rank-one outer product `|u⟩⟨u|`.
* `uniformSuperposition n` (`= |ψ⟩`), the equally-weighted superposition (6.4).
* `amplitudeMean v` (`= ⟨α⟩`) and `inversionAboutMean n` (`= 2|ψ⟩⟨ψ| − I`).
* `inversionAboutMean_mulVec_apply` — **the exercise**: the `k`-th component of
  `(2|ψ⟩⟨ψ| − I) v` equals `−vₖ + 2⟨α⟩` (Eq. 6.7).
-/

namespace AxQM.Concrete

open Matrix

/-- The **reflection operator** `2|u⟩⟨u| − I` as an `n × n` complex matrix, where the
outer product `|u⟩⟨u|` is `Matrix.vecMulVec u (star u)`. For a unit vector `u` this is the
reflection about the line `ℂ · u`. -/
noncomputable def reflectionMatrix {n : ℕ} (u : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (2 : ℂ) • vecMulVec u (star u) - 1

/-- The **equally-weighted superposition** `|ψ⟩ = (1/√N) ∑ₓ|x⟩` (N&C Eq. 6.4), as the
column vector in `ℂ^N` all of whose components equal `(√N)⁻¹`. -/
noncomputable def uniformSuperposition (n : ℕ) : Fin n → ℂ :=
  Function.const (Fin n) ((Real.sqrt n : ℂ))⁻¹

/-- The **mean of the amplitudes** `⟨α⟩ ≡ (∑ₖ αₖ)/N` of a vector `v = ∑ₖ αₖ|k⟩`. -/
noncomputable def amplitudeMean {n : ℕ} (v : Fin n → ℂ) : ℂ := (∑ k, v k) / n

/-- N&C's **inversion-about-the-mean** operator `2|ψ⟩⟨ψ| − I` (Eq. 6.6), the reflection
about the uniform superposition `|ψ⟩`. -/
noncomputable def inversionAboutMean (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  reflectionMatrix (uniformSuperposition n)

/-- **Nielsen & Chuang, Exercise 6.2 / Eq. (6.7).** Applying the inversion-about-the-mean
operator `2|ψ⟩⟨ψ| − I` to a general state `v = ∑ₖ αₖ|k⟩` reflects each amplitude about the
mean: the `k`-th component of `(2|ψ⟩⟨ψ| − I) v` equals `−αₖ + 2⟨α⟩`. -/
theorem inversionAboutMean_mulVec_apply (n : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    (inversionAboutMean n *ᵥ v) k = - v k + 2 * amplitudeMean v := sorry

end AxQM.Concrete
