/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.GeneralizedDepolarizingChannel
import AxQM.Basic.API.ProjectiveMeasurement
import AxQM.Basic.SystemIso

/-!
# AxQM.Basic.API — the computational-basis measurement of a qudit

The **projective measurement of `qudit d` in the computational basis** `{|0⟩, …, |d−1⟩}`, the
final read-out step of the qudit quantum algorithms of Nielsen & Chuang (Chapters 5–6): measuring
the register and reading off which basis state `|i⟩` it collapsed to.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- The **computational-basis (projective) measurement** of `qudit d`: the projective measurement in
the standard basis `{|i⟩}`, with outcome `i : Fin d` the rank-one projector `|i⟩⟨i|` — "the register
was found in the state `|i⟩`". This is N&C's measurement of a register in the computational basis,
the read-out step of the search and other algorithms. -/
def quditMeasurement (d : ℕ) : Measurement (Fin d) (qudit d) :=
  Measurement.ofOrthonormalBasis (quditOrthonormalBasis d)

/-- The computational orthonormal basis is the family of computational-basis pure states:
`quditOrthonormalBasis d i = |i⟩ = (quditBasis i).vec`. -/
theorem quditOrthonormalBasis_apply (i : Fin d) :
    quditOrthonormalBasis d i = (quditBasis i).vec := by
  rw [quditBasis_vec]; exact EuclideanSpace.basisFun_apply (Fin d) ℂ i

/-- **The computational-basis measurement operator is the rank-one projector** `|x⟩⟨x|`. -/
theorem quditMeasurement_op (x : Fin d) :
    (quditMeasurement d).op x
      = InnerProductSpace.rankOne ℂ (quditBasis x).vec (quditBasis x).vec := by
  rw [quditMeasurement, Measurement.ofOrthonormalBasis_op, quditOrthonormalBasis_apply]

end AxQM
