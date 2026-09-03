/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.Finset.Image

/-!
# Concrete: the multiply-controlled NOT as a reversible bit-string permutation (N&C §4.3)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a circuit of `O(n²)` Toffoli, `CNOT` and
single-qubit gates that implements a `Cⁿ(X)` gate — the `n`-controlled `NOT` — **using no work
qubits** (the whole register is the `n` controls and the one target, `n + 1` qubits).
-/

namespace AxQM.Concrete

variable {m : ℕ}

/-- A `Fin 2` bit added to itself cancels. -/
theorem add_add_self_right (b c : Fin 2) : b + c + c = b := by revert b c; decide

/-- Bit-strings agreeing on every wire of `B` satisfy the "all controls set" predicate together. -/
theorem forall_mem_eq_one_congr {B : Finset (Fin m)} {x y : Fin m → Fin 2}
    (h : ∀ i ∈ B, x i = y i) : (∀ i ∈ B, x i = 1) ↔ (∀ i ∈ B, y i = 1) :=
  ⟨fun H i hi => h i hi ▸ H i hi, fun H i hi => (h i hi).symm ▸ H i hi⟩

/-- **The control bit of a multiply-controlled `NOT`**: `1` when every control wire in the finite
set `S` is set to `1` in the bit-string `x`, and `0` otherwise. This is the amount by which the
target wire is flipped. -/
def ctrlBit (S : Finset (Fin m)) (x : Fin m → Fin 2) : Fin 2 :=
  if ∀ i ∈ S, x i = 1 then 1 else 0

/-- **The classical multiply-controlled `NOT`** `mcNot S t`: the reversible map on bit-strings
`Fin m → Fin 2` that adds the control bit `ctrlBit S x` (XOR, since we are in `Fin 2`) to wire `t`,
leaving every other wire unchanged. For `|S| = 0, 1, 2` this is the `NOT`, `CNOT`, Toffoli gate
respectively; in general it is the classical `C^{|S|}(X)` gate with controls `S` and target `t`. -/
def mcNot (S : Finset (Fin m)) (t : Fin m) (x : Fin m → Fin 2) : Fin m → Fin 2 :=
  Function.update x t (x t + ctrlBit S x)

/-- The value of `mcNot S t x` on the target wire `t` is `x t` flipped by the control bit. -/
@[simp] theorem mcNot_apply_self (S : Finset (Fin m)) (t : Fin m) (x : Fin m → Fin 2) :
    mcNot S t x t = x t + ctrlBit S x := by
  simp [mcNot]

/-- The value of `mcNot S t x` on any wire other than the target `t` is unchanged. -/
theorem mcNot_apply_of_ne (S : Finset (Fin m)) (t : Fin m) (x : Fin m → Fin 2) {j : Fin m}
    (h : j ≠ t) : mcNot S t x j = x j := by
  simp only [mcNot, Function.update_of_ne h]

/-- `ctrlBit S` only reads the wires in `S`, so updating a wire outside `S` leaves it unchanged. -/
theorem ctrlBit_update_of_notMem (S : Finset (Fin m)) {j : Fin m} (hj : j ∉ S)
    (x : Fin m → Fin 2) (v : Fin 2) :
    ctrlBit S (Function.update x j v) = ctrlBit S x := by
  simp only [ctrlBit, forall_mem_eq_one_congr
    fun i hi => Function.update_of_ne (fun (h : i = j) => hj (h ▸ hi)) v x]

/-- **`mcNot S t` is an involution** when the target `t` is not one of the controls. -/
theorem mcNot_involutive (S : Finset (Fin m)) {t : Fin m} (ht : t ∉ S) :
    Function.Involutive (mcNot S t) := by
  intro x
  have hc : ctrlBit S (mcNot S t x) = ctrlBit S x :=
    ctrlBit_update_of_notMem S ht x _
  funext j
  by_cases hj : j = t
  · subst hj
    rw [mcNot_apply_self, hc, mcNot_apply_self]
    exact add_add_self_right _ _
  · rw [mcNot_apply_of_ne _ _ _ hj, mcNot_apply_of_ne _ _ _ hj]

/-- **The multiply-controlled `NOT` as a permutation** of the computational basis (when the target
is not a control). -/
def mcNotPerm (S : Finset (Fin m)) {t : Fin m} (ht : t ∉ S) : Equiv.Perm (Fin m → Fin 2) :=
  (mcNot_involutive S ht).toPerm _

end AxQM.Concrete
