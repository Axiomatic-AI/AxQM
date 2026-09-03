/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelLowerBound

/-!
# Concrete: the Grover conditional phase shift `2|0⟩⟨0| − I` (N&C Exercise 6.1)

Nielsen & Chuang, §6.1.2, eq. (6.5) (p. 250–251): step (3) of the Grover iteration performs a
**conditional phase shift** on the `n`-qubit register, with every computational basis state except
`|0⟩` receiving a phase of `−1`,
`|x⟩ ↦ -(-1)^{δ_{x0}} |x⟩`
(so `|0⟩` is fixed and every other basis state is negated). **Exercise 6.1** asks to show that the
unitary operator realising this phase shift is `2|0⟩⟨0| − I`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- **The Grover conditional phase shift** (Nielsen & Chuang eq. (6.5)): the `(d+1) × (d+1)`
operator that fixes `|0⟩` and negates every other computational basis state, i.e. the diagonal
matrix `diag(1, −1, …, −1)`. -/
def groverPhaseShift (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.diagonal fun x => if x = 0 then 1 else -1

/-- **Nielsen & Chuang, Exercise 6.1.** The Grover conditional phase shift equals `2|0⟩⟨0| − I`,
where `|0⟩⟨0| = vecMulVec |0⟩ ⟨0|` is the rank-one projector onto the computational basis state
`|0⟩` (the outer product of `|0⟩ = stdVec 0` with its conjugate transpose
`⟨0| = star (stdVec 0)`). -/
theorem groverPhaseShift_eq_two_ketBraZero_sub_one :
    groverPhaseShift d
      = (2 : ℂ) • Matrix.vecMulVec (stdVec 0) (star (stdVec 0)) - 1 := sorry

end AxQM.Concrete
