/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerGeneratorFlip

/-!
# Concrete: the symplectic-matrix commutation criterion (Nielsen & Chuang, Exercise 10.33)

The **explicit matrix form** of Nielsen & Chuang, Exercise 10.33 — two Pauli-group elements commute
iff the *twisted inner product* `r(g) Λ r(g′)ᵀ` of their check-matrix rows vanishes mod 2, with the
symplectic form `Λ` written out as the literal block **matrix**.

## Main results
* `pauliString_commute_iff_symplecticForm` — **Nielsen & Chuang, Exercise 10.33** in its matrix
  form: `Commute P_g P_h ↔ r(g) Λ r(h)ᵀ = 0`.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- The `2n`-dimensional **check-matrix row** `r(g) = (x_g | z_g)` of a Pauli string as a single
flat vector over `Fin n ⊕ Fin n` and `ZMod 2` (Nielsen & Chuang §10.5.1): the `inl k` coordinate is
the `X`-bit and the `inr k` coordinate the `Z`-bit of the `k`-th single-qubit Pauli `g k`. This is
the `2n`-vector N&C writes `r(g)`. -/
def checkVec (g : Fin n → Fin 4) : Fin n ⊕ Fin n → ZMod 2 :=
  Sum.elim (checkRow g).1 (checkRow g).2

/-- The **symplectic form matrix** `Λ = [[0, I], [I, 0]]` (Nielsen & Chuang eq. (10.84)), the
`2N × 2N` matrix over `ZMod 2` with `N × N` zero blocks on the diagonal and identity blocks on the
off-diagonal, written literally as `Matrix.fromBlocks 0 1 1 0` on the `ι ⊕ ι` decomposition of the
`2N` coordinates (`N = |ι|`). It exchanges the `X`- and `Z`-halves of a check vector, encoding the
`(x | z) ↦ (z | x)` swap at the heart of the "twisted" inner product. The index `ι` is left general;
the Pauli-string case is `ι = Fin n`. -/
def symplecticMatrix {ι : Type*} [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  Matrix.fromBlocks 0 1 1 0

/-- The **twisted inner product** `x Λ yᵀ = x ⬝ᵥ (Λ · y)` of two `2N`-vectors over `ZMod 2` (Nielsen
& Chuang §10.5.1, where `x Λ yᵀ` is described as a twisted inner product of the row matrices `x`
and `y`). The coordinate index `ι` is general. -/
def symplecticForm {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι ⊕ ι → ZMod 2) : ZMod 2 :=
  x ⬝ᵥ symplecticMatrix.mulVec y

/-- **Nielsen & Chuang, Exercise 10.33** (the symplectic check-matrix commutation criterion, matrix
form): two Pauli strings commute iff the twisted inner product of their check-matrix rows
vanishes mod 2, `Commute P_g P_h ↔ r(g) Λ r(h)ᵀ = 0`. Because commutation is phase-independent,
the phase-free `pauliString` is the right representative for the Pauli-group element `g`. -/
theorem pauliString_commute_iff_symplecticForm (g h : Fin n → Fin 4) :
    Commute (pauliString g) (pauliString h) ↔ symplecticForm (checkVec g) (checkVec h) = 0 := sorry

end AxQM.Concrete
