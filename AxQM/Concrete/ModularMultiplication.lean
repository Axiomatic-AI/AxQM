/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Concrete: the modular-multiplication operator `U|y⟩ = |xy mod N⟩` is unitary

Nielsen & Chuang, Exercise 5.12 (§5.3.1, p. 227): the quantum order-finding algorithm applies phase
estimation to the operator `U|y⟩ = |xy (mod N)⟩` (Eq. 5.36).

## Contents

* `modMulIndex` / `modMulPerm` — the register-index map `y ↦ xy (mod N)` (identity for `y ≥ N`) and,
  once `x` is co-prime to `N`, the permutation of `Fin d` it defines.
* `modMulMatrix` — the operator `U` as the permutation matrix of `modMulPerm` over `ℂ`.
* `modMulMatrix_mem_unitaryGroup` — **Exercise 5.12**: `U` is unitary.
-/

open scoped Matrix

namespace AxQM.Concrete

/-- The register-index map underlying N&C's order-finding operator `U|y⟩ = |xy (mod N)⟩`
(Eq. 5.36): on residues `y < N` it is `y ↦ xy (mod N)`, and it fixes `y ≥ N`, matching N&C's
convention on the register `{0, …, d - 1}` (`d = 2ᴸ`). Well-defined for any `N ≤ d`, since
`xy (mod N) < N ≤ d`. -/
def modMulIndex (x : ℕ) {N d : ℕ} (hNd : N ≤ d) (y : Fin d) : Fin d :=
  if h : (y : ℕ) < N then
    ⟨x * (y : ℕ) % N, (Nat.mod_lt _ ((Nat.zero_le _).trans_lt h)).trans_le hNd⟩
  else y

/-- On a residue `y < N`, the index map is `y ↦ xy (mod N)`. -/
theorem modMulIndex_apply_of_lt (x : ℕ) {N d : ℕ} (hNd : N ≤ d) {y : Fin d} (h : (y : ℕ) < N) :
    (modMulIndex x hNd y : ℕ) = x * (y : ℕ) % N := by
  simp only [modMulIndex, dif_pos h]

/-- On `y ≥ N` the index map is the identity (N&C's convention). -/
theorem modMulIndex_apply_of_le (x : ℕ) {N d : ℕ} (hNd : N ≤ d) {y : Fin d} (h : N ≤ (y : ℕ)) :
    modMulIndex x hNd y = y := by
  simp only [modMulIndex, dif_neg (not_lt.mpr h)]

/-- **The identity-extended residue-bijection pattern.** A self-map `f` of the register `Fin d`
that (i) sends every residue `k < N` into `< N`, (ii) fixes every `k ≥ N`, and (iii) is injective on
the residues is injective on all of `Fin d`. -/
theorem injective_of_residue (N : ℕ) {d : ℕ} {f : Fin d → Fin d}
    (hlt : ∀ k : Fin d, (k : ℕ) < N → (f k : ℕ) < N)
    (hfix : ∀ k : Fin d, N ≤ (k : ℕ) → f k = k)
    (hres : ∀ a b : Fin d, (a : ℕ) < N → (b : ℕ) < N → f a = f b → a = b) :
    Function.Injective f := by
  -- a residue `< N` and a fixed point `≥ N` land in disjoint ranges, so cannot be identified
  have mixed : ∀ u v : Fin d, (u : ℕ) < N → ¬ (v : ℕ) < N → f u ≠ f v := by
    intro u v hu hv h
    have h1 : (f u : ℕ) < N := hlt u hu
    rw [hfix v (not_lt.mp hv)] at h
    rw [h] at h1
    exact absurd h1 hv
  intro a b hab
  by_cases ha : (a : ℕ) < N <;> by_cases hb : (b : ℕ) < N
  · exact hres a b ha hb hab
  · exact absurd hab (mixed a b ha hb)
  · exact absurd hab.symm (mixed b a hb ha)
  · rw [hfix a (not_lt.mp ha), hfix b (not_lt.mp hb)] at hab; exact hab

/-- When `x` is co-prime to `N`, the index map is injective (Exercise 5.12). -/
theorem modMulIndex_injective (x : ℕ) {N d : ℕ} (hx : x.Coprime N) (hNd : N ≤ d) :
    Function.Injective (modMulIndex x hNd) := by
  refine injective_of_residue N (fun k hk => ?_) (fun k hk => modMulIndex_apply_of_le x hNd hk)
    (fun a b ha hb hab => ?_)
  · rw [modMulIndex_apply_of_lt x hNd hk]
    exact Nat.mod_lt _ ((Nat.zero_le _).trans_lt hk)
  · -- both residues: cancel the coprime factor `x` mod `N`
    have e : x * (a : ℕ) % N = x * (b : ℕ) % N := by
      rw [← modMulIndex_apply_of_lt x hNd ha, ← modMulIndex_apply_of_lt x hNd hb, hab]
    refine Fin.ext ?_
    rw [← Nat.mod_eq_of_lt ha, ← Nat.mod_eq_of_lt hb]
    exact Nat.ModEq.cancel_left_of_coprime hx.symm e

/-- N&C's order-finding operator `U|y⟩ = |xy (mod N)⟩` as a permutation of the register basis `{0,
…, d - 1}` (`d = 2ᴸ`). -/
noncomputable def modMulPerm (x : ℕ) {N d : ℕ} (hx : x.Coprime N) (hNd : N ≤ d) :
    Equiv.Perm (Fin d) :=
  Equiv.ofBijective (modMulIndex x hNd)
    (Finite.injective_iff_bijective.mp (modMulIndex_injective x hx hNd))

/-- N&C's order-finding operator `U` (Eq. 5.36) as the permutation matrix of `modMulPerm` over `ℂ`,
on the register `{0, …, d - 1}`. -/
noncomputable def modMulMatrix (x : ℕ) {N d : ℕ} (hx : x.Coprime N) (hNd : N ≤ d) :
    Matrix (Fin d) (Fin d) ℂ := (modMulPerm x hx hNd).permMatrix ℂ

/-- **Nielsen & Chuang, Exercise 5.12.** The order-finding operator `U|y⟩ = |xy (mod N)⟩` is
unitary, for any register dimension `d ≥ N`. -/
theorem modMulMatrix_mem_unitaryGroup (x : ℕ) {N d : ℕ} (hx : x.Coprime N) (hNd : N ≤ d) :
    modMulMatrix x hx hNd ∈ Matrix.unitaryGroup (Fin d) ℂ := sorry

end AxQM.Concrete
