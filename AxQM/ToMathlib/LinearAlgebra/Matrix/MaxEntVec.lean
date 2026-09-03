/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.Data.Complex.Basic

/-! # The maximally entangled vector and the Hilbert–Schmidt pairing

Fix a finite index type `n` and a ring `R`. The **(unnormalised) maximally entangled vector**
`|m⟩ = ∑ᵢ eᵢ ⊗ eᵢ`, indexed by `n × n`, is exactly the vectorisation `Matrix.vec` of the identity
matrix. This file records that vector as `Matrix.maxEntVec` and proves that the sesquilinear pairing
`⟨m| (A ⊗ B) |m⟩` of the identity applied to a Kronecker product collapses to a single trace.

## Main results

* `Matrix.star_maxEntVec_dotProduct_kronecker` — the identity
  `⟨m| (A ⊗ₖ B) |m⟩ = tr(Aᵀ * B)`, written as
  `star (maxEntVec n R) ⬝ᵥ ((A ⊗ₖ B).mulVec (maxEntVec n R)) = (Aᵀ * B).trace`. Here
  `star _ ⬝ᵥ _` is the standard sesquilinear pairing of vectors (the bra–ket `⟨·|·⟩`), so the left
  side is the expectation value of the operator `A ⊗ B` in the maximally entangled state `|m⟩`.
* `Matrix.not_forall_trace_conjTranspose_mul_eq_star_maxEntVec_dotProduct_kronecker` — the sharpness
  counterexample: the literal Nielsen & Chuang form `tr(Aᴴ * B) = ⟨m|(A ⊗ B)|m⟩` (with the plain,
  unconjugated `A`) is **false** over `ℂ`.
-/

@[expose] public section

open scoped Kronecker Matrix

namespace Matrix

variable {n : Type*} {R : Type*}

/-- The (unnormalised) **maximally entangled vector** `|m⟩ = ∑ᵢ eᵢ ⊗ eᵢ` on `n × n`, defined as the
vectorisation `Matrix.vec` of the identity matrix `1 : Matrix n n R`. (Nielsen & Chuang,
Exercise 9.16, write this as `|m⟩ = ∑ᵢ |i_R⟩|i_Q⟩`.) -/
def maxEntVec (n R : Type*) [DecidableEq n] [Zero R] [One R] : n × n → R :=
  (1 : Matrix n n R).vec

/-- **The Hilbert–Schmidt pairing via the maximally entangled vector** (Nielsen & Chuang,
Exercise 9.16, in its honest transpose form). The expectation value of a Kronecker product
`A ⊗ B` in the maximally entangled state `|m⟩ = ∑ᵢ eᵢ ⊗ eᵢ` is the trace `tr(Aᵀ * B)`:
`⟨m| (A ⊗ₖ B) |m⟩ = tr(Aᵀ * B)`, where `star _ ⬝ᵥ _` is the standard sesquilinear (bra–ket)
pairing of vectors. (N&C write the right side as `tr(Aᴴ * B)`, but with the standard adjoint the
always-true identity uses the transpose; the two coincide iff `A` is real.) -/
theorem star_maxEntVec_dotProduct_kronecker [Fintype n] [DecidableEq n] [CommRing R] [StarRing R]
    (A B : Matrix n n R) :
    star (maxEntVec n R) ⬝ᵥ ((A ⊗ₖ B).mulVec (maxEntVec n R)) = (Aᵀ * B).trace := sorry

/-- **Sharpness: Nielsen & Chuang's literal `tr(A† B)` form is false.** N&C, Exercise 9.16, write
the identity as `tr(Aᴴ * B) = ⟨m|(A ⊗ B)|m⟩` with the plain, unconjugated `A`. Over `ℂ` that
literal claim fails. -/
theorem not_forall_trace_conjTranspose_mul_eq_star_maxEntVec_dotProduct_kronecker :
    ¬ ∀ A B : Matrix (Fin 1) (Fin 1) ℂ,
      (Aᴴ * B).trace = star (maxEntVec (Fin 1) ℂ) ⬝ᵥ ((A ⊗ₖ B).mulVec (maxEntVec (Fin 1) ℂ)) :=
        sorry

end Matrix
