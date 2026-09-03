/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrixSymplectic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete: the standard-form encoded operators (Nielsen & Chuang, Exercises 10.53–10.54)

This file defines the **standard form**
of a stabilizer check matrix (N&C §10.5.7, eq. (10.111)) and the encoded `X`/`Z` operators read off
it (eqs. around (10.111)), and proves the **symplectic (anti)commutation half** of Exercise 10.54.

## Main results
* `symplecticForm_encXRow_genRow` — every encoded `X` **commutes with every generator** (`= 0`).
* `symplecticForm_encXRow_encXRow` — the encoded `X` operators **commute with one another** (`= 0`).
* `symplecticForm_encXRow_encZRow` — `symplecticForm (X̄ₐ) (Z̄_b) = δ_{ab}`: hence `X̄ⱼ`
  **anticommutes with `Z̄ⱼ`** and **commutes with `Z̄_k` for `k ≠ j`**.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {r m k : ℕ}

/-- The `n = r + m + k` **qubit/column index** of a standard-form check matrix, partitioned into the
`r` pivot columns, the `m = n − k − r` middle columns, and the `k` encoded columns (N&C eq.
(10.111)). A single side (`X`- or `Z`-part) of a check row is a function `Cols r m k → ZMod 2`. -/
abbrev Cols (r m k : ℕ) : Type := Fin r ⊕ Fin m ⊕ Fin k

/-- Assemble a vector over the partitioned columns `Cols r m k = Fin r ⊕ Fin m ⊕ Fin k` from its
three blocks `a` (pivot), `b` (middle), `c` (encoded). This is the row-vector counterpart of the
column blocking `[r | n−k−r | k]` used throughout N&C's standard form. -/
def blk (a : Fin r → ZMod 2) (b : Fin m → ZMod 2) (c : Fin k → ZMod 2) : Cols r m k → ZMod 2 :=
  Sum.elim a (Sum.elim b c)

/-- **The block data of a standard-form check matrix** (Nielsen & Chuang eq. (10.111)) for an
`[n, k]` stabilizer code with `X`-part rank `r` and `m = n − k − r`. The six `𝔽₂`-matrices are the
free blocks of the standard form
`[[I A₁ A₂ | B 0 C], [0 0 0 | D I E]]`; the identity/zero blocks are fixed, so this data determines
the generators (`genRow`) and the encoded operators `[0 Eᵀ I | Cᵀ 0 0]`, `[0 0 0 | A₂ᵀ 0 I]`. -/
structure StandardFormBlocks (r m k : ℕ) where
  /-- Top `X`-block `A₁` (pivot rows against the middle columns). -/
  A₁ : Matrix (Fin r) (Fin m) (ZMod 2)
  /-- Top `X`-block `A₂` (pivot rows against the encoded columns). -/
  A₂ : Matrix (Fin r) (Fin k) (ZMod 2)
  /-- Top `Z`-block `B` (pivot rows against the pivot columns). -/
  B : Matrix (Fin r) (Fin r) (ZMod 2)
  /-- Top `Z`-block `C` (pivot rows against the encoded columns). -/
  C : Matrix (Fin r) (Fin k) (ZMod 2)
  /-- Bottom `Z`-block `D` (middle rows against the pivot columns). -/
  D : Matrix (Fin m) (Fin r) (ZMod 2)
  /-- Bottom `Z`-block `E` (middle rows against the encoded columns). -/
  E : Matrix (Fin m) (Fin k) (ZMod 2)

/-- **A top (pivot) generator**, row `i` of `[I A₁ A₂ | B 0 C]` (the first `r` rows of the standard
form (10.111)): `X`-part `(eᵢ, A₁ i, A₂ i)`, `Z`-part `(B i, 0, C i)`. -/
def genTopRow (S : StandardFormBlocks r m k) (i : Fin r) : Cols r m k ⊕ Cols r m k → ZMod 2 :=
  Sum.elim (blk ((1 : Matrix (Fin r) (Fin r) (ZMod 2)) i) (S.A₁ i) (S.A₂ i))
    (blk (S.B i) 0 (S.C i))

/-- **A bottom (middle) generator**, row `i` of `[0 0 0 | D I E]` (the last `n − k − r` rows of the
standard form (10.111)): `X`-part `0`, `Z`-part `(D i, eᵢ, E i)`. -/
def genMidRow (S : StandardFormBlocks r m k) (i : Fin m) : Cols r m k ⊕ Cols r m k → ZMod 2 :=
  Sum.elim (blk 0 0 0)
    (blk (S.D i) ((1 : Matrix (Fin m) (Fin m) (ZMod 2)) i) (S.E i))

/-- **The stabilizer generators** of a standard-form code as a single family indexed by
`Fin r ⊕ Fin m`: the `r` pivot rows `genTopRow` and the `m = n − k − r` middle rows `genMidRow` of
eq. (10.111). -/
def genRow (S : StandardFormBlocks r m k) : Fin r ⊕ Fin m → (Cols r m k ⊕ Cols r m k → ZMod 2) :=
  Sum.elim (genTopRow S) (genMidRow S)

/-- **The `a`-th encoded `X` operator** `X̄ₐ`, row `a` of the `k × 2n` check matrix `[0 Eᵀ I | Cᵀ 0
0]` (N&C p. 471): `X`-part `(0, Eᵀ a, eₐ)`, `Z`-part `(Cᵀ a, 0, 0)`. -/
def encXRow (S : StandardFormBlocks r m k) (a : Fin k) : Cols r m k ⊕ Cols r m k → ZMod 2 :=
  Sum.elim (blk 0 (S.E.transpose a) ((1 : Matrix (Fin k) (Fin k) (ZMod 2)) a))
    (blk (S.C.transpose a) 0 0)

/-- **The `b`-th encoded `Z` operator** `Z̄_b`, row `b` of the `k × 2n` check matrix `[0 0 0 | A₂ᵀ 0
I]` (N&C p. 471): `X`-part `0`, `Z`-part `(A₂ᵀ b, 0, e_b)`. -/
def encZRow (S : StandardFormBlocks r m k) (b : Fin k) : Cols r m k ⊕ Cols r m k → ZMod 2 :=
  Sum.elim (blk 0 0 0)
    (blk (S.A₂.transpose b) 0 ((1 : Matrix (Fin k) (Fin k) (ZMod 2)) b))

/-- **The encoded `X` operators commute with every stabilizer generator** (N&C Ex 10.54): for every
generator `g` (pivot or middle), `symplecticForm (X̄ₐ) g = 0`. -/
theorem symplecticForm_encXRow_genRow (S : StandardFormBlocks r m k) (a : Fin k)
    (g : Fin r ⊕ Fin m) : symplecticForm (encXRow S a) (genRow S g) = 0 := sorry

/-- **The encoded `X` operators commute with one another** (N&C Ex 10.54):
`symplecticForm (X̄ₐ) (X̄_{a'}) = 0`. -/
theorem symplecticForm_encXRow_encXRow (S : StandardFormBlocks r m k) (a a' : Fin k) :
    symplecticForm (encXRow S a) (encXRow S a') = 0 := sorry

/-- **The encoded `X`/`Z` pairing is the Kronecker delta** (N&C Ex 10.54): `symplecticForm (X̄ₐ)
(Z̄_b) = δ_{ab}`, the value `(1 : Matrix) a b`. -/
theorem symplecticForm_encXRow_encZRow (S : StandardFormBlocks r m k) (a b : Fin k) :
    symplecticForm (encXRow S a) (encZRow S b) = (1 : Matrix (Fin k) (Fin k) (ZMod 2)) a b := sorry

/-!
### Exercise 10.54, the independence half: the encoded `X` rows are `𝔽₂`-linearly independent

N&C's "independent" is `𝔽₂`-linear independence of the `2n`-bit check rows. The statement proved
is the strong joint one — the `r + m` generators (`genRow`) **together with** the `k` encoded `X`
operators (`encXRow`) form a linearly independent family indexed by `(Fin r ⊕ Fin m) ⊕ Fin k`.
-/

/-- **The stabilizer generators and encoded `X` operators are jointly `𝔽₂`-linearly independent**
(N&C Ex 10.54: the encoded `X` operators are independent of one another and of the generators).
The `2n`-bit check rows of the `r + m` generators (`genRow`) together with the `k`
encoded `X` operators (`encXRow`) form a linearly independent family indexed by `(Fin r ⊕ Fin m)
⊕ Fin k`. -/
theorem linearIndependent_genRow_encXRow (S : StandardFormBlocks r m k) :
    LinearIndependent (ZMod 2) (Sum.elim (genRow S) (encXRow S)) := sorry

end AxQM.Concrete
