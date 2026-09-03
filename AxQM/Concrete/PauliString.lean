/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli
import AxQM.ToMathlib.Analysis.Matrix.HilbertSchmidt

/-!
# Concrete: the `n`-fold Pauli strings and their trace orthogonality

It builds, for each `n`, the family of **`n`-fold Pauli tensor products** ("Pauli strings") and
proves their trace orthogonality and `ℂ`-linear independence in the `2ⁿ × 2ⁿ` complex matrices.
This is the mathematical content underlying part (2) of Nielsen & Chuang, Problem 4.3
(`H = Σ_g h_g g` with real `h_g`, the sum over all `n`-fold tensor products `g` of
`{I, X, Y, Z}`).

## Main results
* `pauliString` / `pauliString_apply` — the Pauli string and its defining entry formula.
* `pauliString_isHermitian` — each Pauli string is Hermitian.
* `pauliString_trace_mul` — the **trace orthogonality** `tr(P_g P_h) = 2ⁿ δ_{g h}`, the
  `n`-fold Hilbert–Schmidt orthogonality of the Pauli strings.
* `pauliString_linearIndependent` — the `4ⁿ` Pauli strings are `ℂ`-linearly independent.
* `pauliStringStd` / `pauliStringStd_isHermitian` — the same Pauli string reindexed to the flat `Fin
  (2ⁿ)` computational-basis ordering, still Hermitian.
-/

open Matrix Complex

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- The `n`-fold **Pauli string** for `g : Fin n → Fin 4`, the operator on the `n`-qubit
register (index type `Fin n → Fin 2`) whose `(i, j)` entry is the product of the per-qubit Pauli
entries `∏ₖ σ_{gₖ} (iₖ) (jₖ)`. Entrywise, this is the tensor product `σ_{g₀} ⊗ ⋯ ⊗ σ_{g_{n-1}}`. -/
def pauliString (g : Fin n → Fin 4) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun i j => ∏ k, pauli (g k) (i k) (j k)

@[simp]
theorem pauliString_apply (g : Fin n → Fin 4) (i j : Fin n → Fin 2) :
    pauliString g i j = ∏ k, pauli (g k) (i k) (j k) := rfl

/-- Each Pauli string is Hermitian. -/
theorem pauliString_isHermitian (g : Fin n → Fin 4) : (pauliString g).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply, pauliString_apply, pauliString_apply, ← starRingEnd_apply,
    map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [starRingEnd_apply, pauli_conj_apply]

/-- The **all-identity Pauli string** `σ₀ ⊗ ⋯ ⊗ σ₀ = I ⊗ ⋯ ⊗ I` is the identity matrix. -/
theorem pauliString_const_zero : pauliString (n := n) (fun _ => 0) = 1 := by
  ext i j
  rw [pauliString_apply, Matrix.one_apply]
  have h0 : (pauli 0) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  simp only [h0, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg hij]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hij
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- The trace of a product of two matrices given by per-qubit entry products factors over the
qubits: `tr((∏ₖ Aₖ) (∏ₖ Bₖ)) = ∏ₖ tr(Aₖ Bₖ)`, where the two matrices have `(i,j)` entries `∏ₖ
Aₖ(iₖ)(jₖ)` and `∏ₖ Bₖ(iₖ)(jₖ)`. -/
private theorem trace_mul_prodMatrix (A B : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    ((Matrix.of fun i j : Fin n → Fin 2 => ∏ k, A k (i k) (j k)) *
        (Matrix.of fun i j : Fin n → Fin 2 => ∏ k, B k (i k) (j k))).trace
      = ∏ k, (A k * B k).trace := by
  -- RHS: expand each factor `tr(Aₖ Bₖ) = ∑ a, ∑ b, Aₖ a b * Bₖ b a`, then two `prod_univ_sum`
  -- collapse `∏ₖ ∑ₐ ∑_b` into the double sum `∑ᵢ ∑ⱼ ∏ₖ`.
  have hRHS : (∏ k, (A k * B k).trace)
      = ∑ i : Fin n → Fin 2, ∑ j : Fin n → Fin 2,
          ∏ k, A k (i k) (j k) * B k (j k) (i k) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [hRHS]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
    ← Finset.prod_mul_distrib]

/-- **Trace orthogonality of the Pauli strings**: `tr(P_g P_h) = 2ⁿ δ_{g h}`, the `n`-fold
Hilbert–Schmidt orthogonality of the family. -/
theorem pauliString_trace_mul (g h : Fin n → Fin 4) :
    (pauliString g * pauliString h).trace = if g = h then (2 : ℂ) ^ n else 0 := by
  have hfac : (pauliString g * pauliString h).trace
      = ∏ k, (pauli (g k) * pauli (h k)).trace :=
    trace_mul_prodMatrix (fun k => pauli (g k)) (fun k => pauli (h k))
  rw [hfac]
  simp_rw [pauli_trace_mul]
  by_cases hgh : g = h
  · subst hgh; simp
  · rw [if_neg hgh]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hgh
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- **Trace pairing extracts a coefficient**: `tr(P_m * ∑_g c_g • P_g) = c_m · 2ⁿ`. -/
theorem pauliString_trace_mul_sum_smul (c : (Fin n → Fin 4) → ℂ) (m : Fin n → Fin 4) :
    (pauliString m * ∑ g, c g • pauliString g).trace = c m * (2 : ℂ) ^ n := by
  rw [Finset.mul_sum, Matrix.trace_sum, Finset.sum_eq_single m]
  · rw [mul_smul_comm, Matrix.trace_smul, pauliString_trace_mul, if_pos rfl, smul_eq_mul]
  · intro b _ hb
    rw [mul_smul_comm, Matrix.trace_smul, pauliString_trace_mul, if_neg (Ne.symm hb), smul_zero]
  · intro hm; exact absurd (Finset.mem_univ m) hm

/-- The `4ⁿ` Pauli strings are `ℂ`-linearly independent. -/
theorem pauliString_linearIndependent : LinearIndependent ℂ (pauliString (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc m
  have key := pauliString_trace_mul_sum_smul c m
  rw [hc, Matrix.mul_zero, Matrix.trace_zero] at key
  exact (mul_eq_zero.mp key.symm).resolve_right (pow_ne_zero n two_ne_zero)

/-- The `n`-fold **Pauli string on the standard register indexing** `Fin (2ⁿ)`: the matrix
`pauliString g`, reindexed from bit strings `Fin n → Fin 2` to `Fin (2ⁿ)` along
`finFunctionFinEquiv`. Its `(I, J)` entry is `pauliString g (e⁻¹ I) (e⁻¹ J)` for
`e = finFunctionFinEquiv`. This is the same operator as `pauliString g`, expressed on the flat
`Fin (2ⁿ)` computational-basis ordering that the register `EuclideanSpace ℂ (Fin (2ⁿ))` uses. -/
def pauliStringStd (g : Fin n → Fin 4) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (pauliString g).submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm

/-- The standard-indexed Pauli string is **Hermitian**. -/
theorem pauliStringStd_isHermitian (g : Fin n → Fin 4) : (pauliStringStd g).IsHermitian :=
  (pauliString_isHermitian g).submatrix finFunctionFinEquiv.symm

/-- The Pauli strings are **injective** in their index: distinct `g` give distinct operators `P_g`.
-/
theorem pauliString_injective : Function.Injective (pauliString (n := n)) :=
  pauliString_linearIndependent.injective

/-- A Pauli string is the **identity operator** exactly when its index is all-identity: `P_g = I ↔ g
= 0`. -/
theorem pauliString_eq_one_iff (g : Fin n → Fin 4) : pauliString g = 1 ↔ g = 0 := by
  rw [← pauliString_const_zero, pauliString_injective.eq_iff, Pi.zero_def]

end AxQM.Concrete
