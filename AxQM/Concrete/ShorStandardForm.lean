/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrix
import AxQM.Concrete.NineQubitCode
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete: the nine-qubit Shor code check matrix in standard form (Nielsen & Chuang, Ex 10.57)

The check matrix of the nine-qubit Shor code in standard form: Nielsen & Chuang, **Exercise 10.57**
— *give the check matrices for the five and nine qubit codes in standard form* (N&C §10.5.7,
p. 472).

## Main results
* `shorGenIdx`, `shorStdGen` — the Figure-10.11 generators and their standard form, as
  `Fin 9 → Fin 4` Pauli-index strings (`I=0, X=1, Y=2, Z=3`).
* `shorStdGen_xPart_pivot_identity`, `shorStdGen_bottom_xPart_zero`, `shorStdGen_top_zPart_zero`,
  `shorStdGen_zPart_middle_identity` — the certificate that it **is in standard form** (10.111): the
  four fixed blocks — the top-left `I₂`, the zero `X`-part of the bottom six rows, the zero `Z`-part
  of the top two rows (which also witnesses `B = C = 0`), and the bottom-middle `I₆`.
* `shorStdGen_checkRow_span_eq` — the certificate that it is **the same code**: undoing the qubit
  relabeling (`shorStdGenOriginal`), the `𝔽₂`-span of the standard-form check rows equals that of
  the original Figure-10.11 generators' check rows. Since a stabilizer code is exactly the row space
  of its check matrix, this says the standard form (in the relabeled ordering) and the textbook
  generators define the same Shor code.
-/

open Matrix

open scoped BigOperators

-- The check matrix is eight explicit nine-entry Pauli strings; unfolding them entrywise exceeds
-- the default recursion depth.
set_option maxRecDepth 4000

namespace AxQM.Concrete

/-- **The nine-qubit Shor code check matrix in standard form** (Nielsen & Chuang, Exercise 10.57),
as eight `Fin 9 → Fin 4` Pauli-index strings in the relabeled qubit ordering `(1,7,2,3,4,5,8,9,6)`:
```
s₁ = X . X X X X . . X      s₅ = . . . . Z . . . Z
s₂ = . X . . X X X X X      s₆ = . . . . . Z . . Z
s₃ = Z . Z . . . . . .      s₇ = . Z . . . . Z . .
s₄ = Z . . Z . . . . .      s₈ = . Z . . . . . Z .
```
Here `r = 2`, `m = 6`, `k = 1`, the relabeling being `shorStdSwap`. The `X`-part of the top two rows
is `[I₂ A₁ A₂]` and the `Z`-part of the bottom six is `[D I₆ E]`. -/
def shorStdGen : Fin 8 → Fin 9 → Fin 4 :=
  ![![1, 0, 1, 1, 1, 1, 0, 0, 1], ![0, 1, 0, 0, 1, 1, 1, 1, 1], ![3, 0, 3, 0, 0, 0, 0, 0, 0],
    ![3, 0, 0, 3, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 3, 0, 0, 0, 3], ![0, 0, 0, 0, 0, 3, 0, 0, 3],
    ![0, 3, 0, 0, 0, 0, 3, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 3, 0]]

/-- The **qubit relabeling** of Nielsen & Chuang §10.5.7 that brings the Shor code into standard
form: the column permutation reordering the nine qubits as `(1,7,2,3,4,5,8,9,6)` — the two
`X`-pivot columns (original qubits `1, 7`) first, the six `Z`-pivot columns (`2,3,4,5,8,9`) in
the middle, the single free `k`-column (`6`) last. As a `0`-indexed permutation of `Fin 9` it is
the eight-cycle `(1 2 3 4 5 8 7 6)` (fixing `0`), i.e. it sends each original qubit position to
its position in the standard-form ordering. -/
def shorStdSwap : Equiv.Perm (Fin 9) := List.formPerm ([1, 2, 3, 4, 5, 8, 7, 6] : List (Fin 9))

/-- The **standard-form Shor generators translated back to the original qubit ordering**: each
`shorStdGen i` reindexed by the relabeling `shorStdSwap` (precomposition undoes the column
swaps). -/
def shorStdGenOriginal (i : Fin 8) : Fin 9 → Fin 4 := fun k => shorStdGen i (shorStdSwap k)

/-- **The Shor standard form is in standard form** (N&C eq. (10.111)), fixed block 1 — the top-left
`X`-identity: the `X`-part of the top `r = 2` rows, restricted to the first `r = 2` (pivot) columns,
is the `2 × 2` identity — row `i` has a `1` in pivot column `j` iff `i = j`. -/
theorem shorStdGen_xPart_pivot_identity (i : Fin 8) (j : Fin 9) (hi : i.val ≤ 1) (hj : j.val ≤ 1) :
    (checkRow (shorStdGen i)).1 j = if i.val = j.val then 1 else 0 := sorry

/-- **The Shor standard form is in standard form** (N&C eq. (10.111)), fixed block 2 — the zero
`X`-part of the bottom rows: the bottom `m = 6` rows (the pure-`Z` generators) have vanishing
`X`-part `[0 0 0]`. -/
theorem shorStdGen_bottom_xPart_zero (i : Fin 8) (hi : 2 ≤ i.val) :
    (checkRow (shorStdGen i)).1 = 0 := sorry

/-- **The Shor standard form is in standard form** (N&C eq. (10.111)), fixed block 3 — the zero
middle `Z`-block of the top rows: the top `r = 2` rows (the pure-`X` generators) have vanishing
`Z`-part. -/
theorem shorStdGen_top_zPart_zero (i : Fin 8) (hi : i.val ≤ 1) :
    (checkRow (shorStdGen i)).2 = 0 := sorry

/-- **The Shor standard form is in standard form** (N&C eq. (10.111)), fixed block 4 — the
bottom-middle `Z`-identity: the `Z`-part of the bottom `m = 6` rows, restricted to the middle
`m = 6` columns (indices `2,…,7`), is the `6 × 6` identity — row `i` has a `1` in middle column `j`
iff `i = j`. Together with the three preceding blocks this is the full standard-form shape of the
check matrix. -/
theorem shorStdGen_zPart_middle_identity (i : Fin 8) (j : Fin 9)
    (hi : 2 ≤ i.val) (hj1 : 2 ≤ j.val) (hj2 : j.val ≤ 7) :
    (checkRow (shorStdGen i)).2 j = if i.val = j.val then 1 else 0 := sorry

/-- **Nielsen & Chuang, Exercise 10.57 (nine-qubit Shor code): the standard form defines the same
code.** After undoing the qubit relabeling (`shorStdGenOriginal`), the `𝔽₂`-span of the
standard-form check rows equals the span of the original Figure-10.11 generators' check rows.
-/
theorem shorStdGen_checkRow_span_eq :
    Submodule.span (ZMod 2) (Set.range (fun i => checkRow (shorStdGenOriginal i)))
      = Submodule.span (ZMod 2) (Set.range (fun i => checkRow (shorGenIdx i))) := sorry

end AxQM.Concrete
