/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrix
import AxQM.Concrete.SteaneCode

/-!
# Concrete: the standard form of the Steane code and its encoded `X̄` (Nielsen & Chuang, Ex 10.55)

Nielsen & Chuang, **Exercise 10.55** asks for the encoded `X̄` operator of the standard form of
the Steane code (N&C §10.5.7, p. 471).

## Main results
* `steaneStdGen` — the six standard-form generators (10.112) as `Fin 7 → Fin 4` Pauli-index strings
  (`I=0, X=1, Y=2, Z=3`).
* `steaneStdLogicalX_checkRow` — **Exercise 10.55**: the `X̄` recipe `[0 Eᵀ I | Cᵀ 0 0]` applied to
  (10.112) is the check row of `X̄ = X₄X₅X₇`. This is the `X̄` operator for the standard form.
* `steaneStdSwap`, `steaneStdLogicalXOriginal` — undoing the qubit swaps (`1↔4, 3↔4, 6↔7`)
  translates the standard-form `X̄` back to the **original** Steane ordering, `X̄ = X₃X₅X₆`, with
  support word `0010110`.
-/

namespace AxQM.Concrete

/-- The six **standard-form generators** of the Steane code (Nielsen & Chuang eq. (10.112)) as
Pauli-index strings `Fin 7 → Fin 4` (`I=0, X=1, Y=2, Z=3`). The top three rows are `X`-type
(`X`-part `[I A₁ A₂]`, `Z`-part `0`), the bottom three `Z`-type (`X`-part `0`, `Z`-part `[D I
E]`). -/
def steaneStdGen : Fin 6 → Fin 7 → Fin 4 :=
  ![![1, 0, 0, 0, 1, 1, 1],
    ![0, 1, 0, 1, 0, 1, 1],
    ![0, 0, 1, 1, 1, 1, 0],
    ![3, 0, 3, 3, 0, 0, 3],
    ![0, 3, 3, 0, 3, 0, 3],
    ![3, 3, 3, 0, 0, 3, 0]]

/-- The **standard-form encoded `X̄`** of the Steane code (Nielsen & Chuang, **Exercise 10.55**):
`X̄ = X₄X₅X₇`, the operator with check row `[0 Eᵀ I | Cᵀ 0 0]` read off (10.112). -/
def steaneStdLogicalX : Fin 7 → Fin 4 := ![0, 0, 0, 1, 1, 0, 1]

/-- The `k`-column `C` of (10.112), extracted as the `Z`-part qubit-`7` column of the top three
rows. -/
def steaneStdC : Fin 3 → ZMod 2 :=
  ![(checkRow (steaneStdGen 0)).2 6, (checkRow (steaneStdGen 1)).2 6,
    (checkRow (steaneStdGen 2)).2 6]

/-- The `k`-column `E` of (10.112), extracted as the `Z`-part qubit-`7` column of the bottom three
rows. -/
def steaneStdE : Fin 3 → ZMod 2 :=
  ![(checkRow (steaneStdGen 3)).2 6, (checkRow (steaneStdGen 4)).2 6,
    (checkRow (steaneStdGen 5)).2 6]

/-- The **standard-form encoded-`X̄` recipe** `[0 Eᵀ I | Cᵀ 0 0]` (Nielsen & Chuang §10.5.7),
specialised to the Steane parameters `r = 3`, `n − k − r = 3`, `k = 1`. -/
def encodedXBarCheckRow (E C : Fin 3 → ZMod 2) : (Fin 7 → ZMod 2) × (Fin 7 → ZMod 2) :=
  (![0, 0, 0, E 0, E 1, E 2, 1], ![C 0, C 1, C 2, 0, 0, 0, 0])

/-- **Nielsen & Chuang, Exercise 10.55.** The encoded-`X̄` recipe `[0 Eᵀ I | Cᵀ 0 0]` (§10.5.7),
built from the read-offs `E` and `C` of (10.112), is exactly the check row of
`steaneStdLogicalX = X₄X₅X₇`. So the `X̄` operator for the standard form is `X₄X₅X₇`. -/
theorem steaneStdLogicalX_checkRow :
    checkRow steaneStdLogicalX = encodedXBarCheckRow steaneStdE steaneStdC := sorry

/-- The **qubit relabeling** of Nielsen & Chuang §10.5.7 that undoes the swaps bringing the Steane
code into standard form: the composite of the transpositions `1↔4`, `3↔4`, `6↔7` (`0`-indexed
`0↔3`, `2↔3`, `5↔6`). As a permutation `original ↦ standard`, it sends a Pauli string in the
standard ordering back to the original code by precomposition. -/
def steaneStdSwap : Equiv.Perm (Fin 7) :=
  Equiv.swap 5 6 * Equiv.swap 2 3 * Equiv.swap 0 3

/-- **`X̄` in the original Steane ordering** (Nielsen & Chuang, Exercise 10.55): the standard-form
`X̄ = X₄X₅X₇` reindexed by undoing the swaps `steaneStdSwap` (precomposition sends the standard-form
Pauli string back to the original code). -/
def steaneStdLogicalXOriginal : Fin 7 → Fin 4 := fun k => steaneStdLogicalX (steaneStdSwap k)

/-- **The support word of the original-ordering `X̄`**: the `X`-part `(checkRow …).1` of the found
operator `steaneStdLogicalXOriginal = X₃X₅X₆`, i.e. the `ZMod 2` bit vector `0010110`. -/
def steaneStdLogicalXOriginalSupport : Fin 7 → ZMod 2 := (checkRow steaneStdLogicalXOriginal).1

end AxQM.Concrete
