/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ModularMultiplication
import Mathlib.Logic.Equiv.Prod

/-!
# Concrete: the order-finding state via the adder `V` vs. the powers `Uʲ`

Nielsen & Chuang, Exercise 5.14 (§5.3.1, p. 227). The quantum state produced in the order-finding
algorithm *before* the inverse Fourier transform is (Eq. 5.46)

## Contents

* `modShiftIndex` / `modShiftPerm` — the target-register adder `k ↦ (k + c) mod N` (identity for
  `k ≥ N`) and, as a permutation of `Fin d`, the "add the constant `c` modulo `N`" gate.
* `modExpAddPerm` — the joint operator `V` (`V(j, k) = (j, k + xʲ mod N)`).
* `modExpAddMatrix` — `V` as a (unitary) permutation matrix.
* `orderFindingStateU` / `orderFindingStateV` and `orderFindingStateV_eq_orderFindingStateU` —
  **Exercise 5.14:** the `V`-from-`|0⟩` state equals the `Uʲ`-from-`|1⟩` state.
-/

open scoped Matrix

namespace AxQM.Concrete

/-- The register-index map of the target-register adder `k ↦ (k + c) mod N` (Eq. 5.47's second
register). -/
def modShiftIndex (c : ℕ) {N d : ℕ} (hNd : N ≤ d) (k : Fin d) : Fin d :=
  if h : (k : ℕ) < N then
    ⟨((k : ℕ) + c) % N, (Nat.mod_lt _ ((Nat.zero_le _).trans_lt h)).trans_le hNd⟩
  else k

/-- On a residue `k < N`, the adder index map is `k ↦ (k + c) mod N`. -/
theorem modShiftIndex_apply_of_lt (c : ℕ) {N d : ℕ} (hNd : N ≤ d) {k : Fin d} (h : (k : ℕ) < N) :
    (modShiftIndex c hNd k : ℕ) = ((k : ℕ) + c) % N := by simp only [modShiftIndex, dif_pos h]

/-- On `k ≥ N` the adder index map is the identity. -/
theorem modShiftIndex_apply_of_le (c : ℕ) {N d : ℕ} (hNd : N ≤ d) {k : Fin d} (h : N ≤ (k : ℕ)) :
    modShiftIndex c hNd k = k := by simp only [modShiftIndex, dif_neg (not_lt.mpr h)]

/-- The adder index map is injective. (No coprimality needed — a translation is a bijection.) -/
theorem modShiftIndex_injective (c : ℕ) {N d : ℕ} (hNd : N ≤ d) :
    Function.Injective (modShiftIndex c hNd) := by
  refine injective_of_residue N (fun k hk => ?_) (fun k hk => modShiftIndex_apply_of_le c hNd hk)
    (fun a b ha hb hab => ?_)
  · rw [modShiftIndex_apply_of_lt c hNd hk]
    exact Nat.mod_lt _ ((Nat.zero_le _).trans_lt hk)
  · have e : ((a : ℕ) + c) % N = ((b : ℕ) + c) % N := by
      rw [← modShiftIndex_apply_of_lt c hNd ha, ← modShiftIndex_apply_of_lt c hNd hb, hab]
    refine Fin.ext ?_
    have : (a : ℕ) ≡ (b : ℕ) [MOD N] := Nat.ModEq.add_right_cancel' c e
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- The target-register adder "add the constant `c` modulo `N`" as a permutation of the register
`Fin d`, fixing `k ≥ N`. -/
noncomputable def modShiftPerm (c : ℕ) {N d : ℕ} (hNd : N ≤ d) : Equiv.Perm (Fin d) :=
  Equiv.ofBijective (modShiftIndex c hNd)
    (Finite.injective_iff_bijective.mp (modShiftIndex_injective c hNd))

/-- **Exercise 5.14's transform `V`** (Eq. 5.47) as a permutation of the joint register
`Fin m × Fin d`: it fixes the control register `j` and applies to the target register the adder
`modShiftPerm (xʲ mod N)`, i.e. `V(j, k) = (j, k + xʲ mod N)`. Being a permutation is exactly what
makes `V` "a different unitary transform". -/
noncomputable def modExpAddPerm (x : ℕ) {N d : ℕ} (hNd : N ≤ d) (m : ℕ) :
    Equiv.Perm (Fin m × Fin d) :=
  Equiv.prodCongrRight (fun j : Fin m => modShiftPerm (x ^ (j : ℕ) % N) hNd)

/-- **Exercise 5.14's transform `V` as a (unitary) permutation matrix.** `Matrix.permMatrixHom`
represents `V` with the forward action `V|q⟩ = |modExpAddPerm q⟩`. -/
noncomputable def modExpAddMatrix (x : ℕ) {N d : ℕ} (hNd : N ≤ d) (m : ℕ) :
    Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ :=
  Matrix.permMatrixHom (modExpAddPerm x hNd m)

/-- The order-finding state **from the powers `Uʲ`** (Eq. 5.46), `∑ⱼ |j⟩ Uʲ|1⟩`, with the target
register started in `|1⟩`. -/
noncomputable def orderFindingStateU (x : ℕ) {N d : ℕ} [NeZero d] (hx : x.Coprime N) (hNd : N ≤ d)
    (m : ℕ) : (Fin m × Fin d) → ℂ :=
  ∑ j : Fin m, Pi.single (j, (modMulPerm x hx hNd ^ (j : ℕ)) (1 : Fin d)) 1

/-- The order-finding state **from the single transform `V`**. -/
noncomputable def orderFindingStateV (x : ℕ) {N d : ℕ} [NeZero d] (hNd : N ≤ d) (m : ℕ) :
    (Fin m × Fin d) → ℂ :=
  (modExpAddMatrix x hNd m).mulVec (∑ j : Fin m, Pi.single (j, (0 : Fin d)) 1)

/-- **Nielsen & Chuang, Exercise 5.14.** The order-finding state obtained by applying the single
transform `V` to `∑ⱼ |j⟩|0⟩` equals the state obtained from the powers `Uʲ` on `∑ⱼ |j⟩|1⟩`:

`V ·(∑ⱼ |j⟩|0⟩) = ∑ⱼ |j⟩ Uʲ|1⟩`.
-/
theorem orderFindingStateV_eq_orderFindingStateU (x : ℕ) {N d : ℕ} [NeZero d] (hx : x.Coprime N)
    (hNd : N ≤ d) (hN : 1 < N) (m : ℕ) :
    orderFindingStateV x hNd m = orderFindingStateU x hx hNd m := sorry

end AxQM.Concrete
