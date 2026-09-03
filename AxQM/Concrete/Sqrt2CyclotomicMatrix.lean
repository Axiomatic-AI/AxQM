/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Sqrt2IntegerMatrix
import AxQM.Concrete.PiEighthGate
import Mathlib.NumberTheory.Real.Irrational

/-!
# Concrete: the `T`-gate variant of Exercise 4.45 — the cyclotomic ring `ℤ[ζ₈]`

The **second half of Nielsen &
Chuang, Exercise 4.45** (p. 198). Having shown that a
unitary `U` built from `H, S, CNOT, Toffoli` has the form `2⁻ᵏ⸍² M` with `M` a Gaussian-integer
(`ℤ[i]`) matrix, N&C ask for the same result with the Toffoli gate replaced by the `π/8` gate `T`.
-/

namespace AxQM.Concrete

open Matrix

noncomputable section

variable {m n : Type*}

/-- **The primitive eighth root of unity** `ζ₈ = e^{iπ/4}`, the nontrivial diagonal entry of the
`π/8` gate `T = diag(1, ζ₈)` (`tMatrix`). It satisfies `ζ₈² = i` (`zeta8_sq`), so `ℤ[ζ₈] ⊇ ℤ[i]`;
and `ζ₈ = (1 + i)/√2` is the value that makes the `ℤ[i]` reading of the `T`-variant fail. -/
def zeta8 : ℂ := Complex.exp ((Real.pi / 4 : ℝ) * Complex.I)

/-- `ζ₈² = i`: squaring `e^{iπ/4}` gives `e^{iπ/2} = i`. Hence `ℤ[ζ₈]` contains `ℤ[i]`. -/
theorem zeta8_sq : zeta8 ^ 2 = Complex.I := by
  rw [sq, zeta8, ← Complex.exp_add,
    show ((Real.pi / 4 : ℝ) : ℂ) * Complex.I + ((Real.pi / 4 : ℝ) : ℂ) * Complex.I
      = (↑Real.pi / 2) * Complex.I from by push_cast; ring]
  exact Complex.exp_pi_div_two_mul_I

/-- **The cyclotomic integers `ℤ[ζ₈] ⊆ ℂ`** for `ζ₈ = e^{iπ/4}` — the entry ring of the
`H, S, CNOT, T` variant of Exercise 4.45. Because `ζ₈² = i`, every element is uniquely a
Gaussian-integer combination `p + q·ζ₈` of `1` and `ζ₈` (`p, q ∈ ℤ[i]`); equivalently a
complex-integer combination `a + b·ζ₈ + c·ζ₈² + d·ζ₈³` of the eighth roots of unity. Closure
under multiplication is immediate from `ζ₈² = i`:
`(p + q ζ₈)(p' + q' ζ₈) = (p p' + i q q') + (p q' + p' q) ζ₈`. -/
def cyclotomicIntSubring : Subring ℂ where
  carrier := {z | ∃ p q : ℂ, p ∈ gaussianIntSubring ∧ q ∈ gaussianIntSubring ∧ z = p + q * zeta8}
  zero_mem' := ⟨0, 0, gaussianIntSubring.zero_mem, gaussianIntSubring.zero_mem, by ring⟩
  one_mem' := ⟨1, 0, gaussianIntSubring.one_mem, gaussianIntSubring.zero_mem, by ring⟩
  add_mem' := by
    rintro x y ⟨p, q, hp, hq, rfl⟩ ⟨p', q', hp', hq', rfl⟩
    exact ⟨p + p', q + q', add_mem hp hp', add_mem hq hq', by ring⟩
  mul_mem' := by
    rintro x y ⟨p, q, hp, hq, rfl⟩ ⟨p', q', hp', hq', rfl⟩
    refine ⟨p * p' + q * q' * Complex.I, p * q' + p' * q, ?_, ?_, ?_⟩
    · exact add_mem (mul_mem hp hp') (mul_mem (mul_mem hq hq') complexI_mem_gaussianIntSubring)
    · exact add_mem (mul_mem hp hq') (mul_mem hp' hq)
    · linear_combination (q * q') * zeta8_sq
  neg_mem' := by
    rintro x ⟨p, q, hp, hq, rfl⟩
    exact ⟨-p, -q, neg_mem hp, neg_mem hq, by ring⟩

/-- **Nielsen & Chuang, Exercise 4.45 (`H, S, CNOT, T`).** The unitary of any circuit — the product
`L.prod` of a list `L` of matrices each of which is a `√2`-scaled `ℤ[ζ₈]` matrix (e.g. an embedded
`H`/`S`/`CNOT`/`T` gate) — has the form `2⁻ᵏ⸍² M` with `M` a `2ⁿ × 2ⁿ` matrix over the cyclotomic
integers `ℤ[ζ₈]`. -/
theorem exists_circuit_form_cyclotomic [Fintype m] [DecidableEq m]
    (L : List (Matrix m m ℂ)) (h : ∀ U ∈ L, IsSqrt2ScaledIn cyclotomicIntSubring U) :
    ∃ (k : ℕ) (M : Matrix m m ℂ),
      (∀ i j, ∃ a b c d : ℤ, M i j = a + b * zeta8 + c * zeta8 ^ 2 + d * zeta8 ^ 3) ∧
        L.prod = (((2 : ℝ) ^ (-(k : ℝ) / 2) : ℝ) : ℂ) • M := sorry

/-- **Nielsen & Chuang, Exercise 4.45, `T`-variant refutation.** The `π/8` gate `T = diag(1,
e^{iπ/4})` is **not** `√2`-scaled over Gaussian integers `ℤ[i]`. Reading the two diagonal
entries of such an `M` yields `M₀₀ = (√2)ᵏ` and `M₁₁ = (√2)ᵏ · ζ₈`, whose product `M₀₀ · M₁₁ =
2ᵏ · ζ₈` is a Gaussian integer; taking real parts gives `2ᵏ · (√2/2) = a` for an integer `a`,
i.e. `√2 = 2a / 2ᵏ` is rational — contradicting `irrational_sqrt_two`. -/
theorem not_isSqrt2ScaledIn_gaussian_tMatrix :
    ¬ IsSqrt2ScaledIn gaussianIntSubring tMatrix := sorry

end

end AxQM.Concrete
