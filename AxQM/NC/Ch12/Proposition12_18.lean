/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.PartialTrace
import AxQM.Basic.Composite
import AxQM.ToMathlib.Analysis.InnerProductSpace.Purification
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.PureState
import AxQM.ToMathlib.Analysis.InnerProductSpace.EuclideanConjVec
import AxQM.ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl

/-!
# Nielsen & Chuang, Proposition 12.18 (information gain implies disturbance)

*(N&C p. 586.)*

Information gain implies disturbance for non-orthogonal quantum states.

* `informationGain_implies_disturbance` — the contrapositive that gives the proposition its name: if
  the probe *gains information* (its two ancilla outcomes differ, `v ≠ v'`) then the simultaneous
  no-disturbance forms `U(ψ ⊗ u) = ψ ⊗ v`, `U(φ ⊗ u) = φ ⊗ v'` cannot both hold — i.e. at least one
  signal must be disturbed.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S A : QSystem}

/-- **Proposition 12.18 (information gain implies disturbance).** The contrapositive reading that
gives the proposition its name. For non-orthogonal signal states `ψ, φ` (`ψ.overlap φ ≠ 0`) and
a unitary probe `U` on `S ⊗ A` with ancilla prepared in `u`, if the probe *gains information* —
its two possible ancilla outcomes `v, v'` differ — then the signal cannot have been left
undisturbed in both cases: the simultaneous no-disturbance forms `U(ψ ⊗ u) = ψ ⊗ v` and `U(φ ⊗
u) = φ ⊗ v'` cannot both hold. Information gain is possible only at the expense of disturbing
the signal. -/
theorem informationGain_implies_disturbance
    {ψ φ : PureState S} {u v v' : PureState A} {U : Evolution (S ⊗ A)}
    (hnonorth : ψ.overlap φ ≠ 0) (hgain : v ≠ v') :
    ¬ (U.evolvePure (ψ ⊗ u) = ψ ⊗ v ∧ U.evolvePure (φ ⊗ u) = φ ⊗ v') := sorry

end AxQM
