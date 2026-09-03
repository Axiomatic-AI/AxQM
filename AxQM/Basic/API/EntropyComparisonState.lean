/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BlochState
import AxQM.Basic.API.Mixture
import AxQM.Concrete.BlochMatrix
import AxQM.ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM
import AxQM.ToMathlib.Analysis.InnerProductSpace.TraceNorm

/-!
# AxQM.Basic.API — the mixed qubit state of Nielsen & Chuang Exercise 11.12

Nielsen & Chuang, Exercise 11.12 (*Comparison of quantum and classical entropies*) forms the
one-parameter family of **mixed qubit states**

## Main definitions

* `entropyComparisonState p hp0 hp1` — the state `ρ(p) = p |0⟩⟨0| + (1 − p) |+⟩⟨+|`, as the binary
  mixture `State.mixPair` of the two Bloch pure states.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

open Matrix ContinuousLinearMap

/-- **The Nielsen & Chuang Exercise 11.12 state** `ρ(p) = p |0⟩⟨0| + (1 − p) |+⟩⟨+|`: the binary
probabilistic mixture (`State.mixPair`) of the two pure states `|0⟩⟨0| = blochState ![0, 0, 1]`
and `|+⟩⟨+| = blochState ![1, 0, 0]` with weights `p` and `1 − p`. -/
def entropyComparisonState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : State qubit :=
  State.mixPair hp0 hp1
    (blochState ![0, 0, 1] (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two]))
    (blochState ![1, 0, 0] (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two]))

end AxQM
