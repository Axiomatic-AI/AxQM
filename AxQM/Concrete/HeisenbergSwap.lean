/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DipolarCoupling
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import AxQM.ToMathlib.Analysis.Normed.Algebra.ExponentialInvolution

/-!
# Concrete: the SWAP and √SWAP gates from the Heisenberg exchange interaction

*Nielsen & Chuang, Exercise 7.52 (Universality of the Heisenberg Hamiltonian), Parts 1 and 2.*

## Main results

* `heisenbergEvolution_pi` — **Part 1.** At `φ = π` the interaction implements a swap operation:
  `exp(−iπ S⃗₁·S⃗₂) = e^{−iπ/4}·SWAP`, i.e. `SWAP` up to the physically irrelevant global phase
  `e^{−iπ/4}`.
* `sqrtSwapHeis_eq` — **Part 2.** At `φ = π/2` (half the time) one obtains the `√SWAP` gate in
  closed form `e^{iπ/8}·(√2/2)·(I − i·SWAP)`.
* `sqrtSwapHeis_mul_self` — `√SWAP² = exp(−iπ S⃗₁·S⃗₂)`, the swap-evolution of Part 1, so
  `sqrtSwapHeis` is genuinely a square root of the swap operation.
-/

open Matrix NormedSpace
open scoped Kronecker BigOperators

namespace AxQM.Concrete

/-- The **two-qubit SWAP gate** `SWAP` as a `4×4` complex matrix on `Fin 2 × Fin 2`: the basis
transposition `|01⟩ ↔ |10⟩` exchanging the two qubits (`SWAP |ab⟩ = |ba⟩`). -/
noncomputable def twoQubitSwap : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.swap ℂ ((0, 1) : Fin 2 × Fin 2) ((1, 0) : Fin 2 × Fin 2)

/-- The dimensionless **Heisenberg coupling operator** `S⃗₁·S⃗₂ = ¼ σ⃗₁·σ⃗₂` (with `S⃗ᵢ = σ⃗ᵢ/2`),
the operator appearing in the exchange Hamiltonian `H = J S⃗₁·S⃗₂` of Nielsen & Chuang (7.174). -/
noncomputable def heisenbergDot : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 4 : ℂ) • spinSpinCoupling

/-- The **Heisenberg time-evolution operator** `exp(−iφ S⃗₁·S⃗₂)`: turning on the exchange
interaction for a (dimensionless) duration `φ`. The swap operation of Part 1 is `φ = π` and the
`√SWAP` gate of Part 2 is `φ = π/2`. -/
noncomputable def heisenbergEvolution (φ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  exp ((-Complex.I * (φ : ℂ)) • heisenbergDot)

/-- **Nielsen & Chuang, Exercise 7.52, Part 1 (the swap operation).** Turning on the Heisenberg
interaction for `φ = π` implements a swap operation:
`exp(−iπ S⃗₁·S⃗₂) = e^{−iπ/4}·SWAP`,
i.e. exactly `SWAP` up to the (physically irrelevant) global phase `e^{−iπ/4}`. -/
theorem heisenbergEvolution_pi :
    heisenbergEvolution Real.pi
      = Complex.exp ((-(Real.pi / 4 : ℝ) : ℂ) * Complex.I) • twoQubitSwap := sorry

/-- The **`√SWAP` gate** obtained by running the Heisenberg interaction for half the swap time,
`√SWAP = exp(−i(π/2) S⃗₁·S⃗₂) = heisenbergEvolution (π/2)`. -/
noncomputable def sqrtSwapHeis : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  heisenbergEvolution (Real.pi / 2)

/-- **Nielsen & Chuang, Exercise 7.52, Part 2 (compute the `√SWAP` transform).** The closed form
`√SWAP = e^{iπ/8}·(√2/2)·(I − i·SWAP)`. -/
theorem sqrtSwapHeis_eq :
    sqrtSwapHeis
      = Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) •
          (((Real.sqrt 2 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
            - (((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I) • twoQubitSwap) := sorry

open scoped Matrix.Norms.Operator in
/-- **`√SWAP` is a square root of the swap operation**: `√SWAP² = exp(−iπ S⃗₁·S⃗₂)`, the
swap-with-phase of Part 1. -/
theorem sqrtSwapHeis_mul_self :
    sqrtSwapHeis * sqrtSwapHeis = heisenbergEvolution Real.pi := sorry

end AxQM.Concrete
