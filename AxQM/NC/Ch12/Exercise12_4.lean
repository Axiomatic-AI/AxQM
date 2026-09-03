/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.HolevoChi
import AxQM.NC.Ch12.Problem12_1
import AxQM.Basic.API.Reflection
import AxQM.Basic.API.Qubit
import AxQM.ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM
import AxQM.Basic.API.ThreeQubitBitFlipCode
import AxQM.Basic.API.BellReducedState
import AxQM.Basic.API.EntropyComposite
import AxQM.Basic.API.Fidelity
import AxQM.Basic.API.TraceDistance
import AxQM.ToMathlib.Analysis.InnerProductSpace.POVM
import AxQM.Concrete.ClassicalTraceDistance
import AxQM.Basic.API.HSOverlap
import AxQM.Basic.API.BlochState
import AxQM.Concrete.BlochMatrix
import AxQM.Concrete.SICQubitEnsemble
import AxQM.ToMathlib.InformationTheory.ConditionalCollisionEntropy

/-!
# Nielsen & Chuang, Exercise 12.4 (the tetrahedral / SIC qubit ensemble)

*(N&C p. 535.)*

For four given pure states, show max mutual info < 1 bit; construct achieving POVM.

* `sicQubitState` — the four pure states `|X₁⟩, …, |X₄⟩` as a family `Fin 4 → PureState qubit`,
  built from the concrete amplitude vectors `Concrete.sicKet` via `qubitSuperposition`.
* `sicProb` — the uniform (equal-weight) distribution over the four states.
* `mutualInfo_sicQubitState_lt_log_two` — for *any* measurement `m`,
  `H(X : Y) < log 2`; i.e. the maximum mutual information is *strictly* less than one bit.
-/

open Complex Matrix

namespace AxQM

/-- The four pure states of Nielsen & Chuang Exercise 12.4 as a family `Fin 4 → PureState qubit`:
`|X₁⟩ = |0⟩` and `|Xₖ₊₁⟩ = √(1/3)(|0⟩ + √2 e^{2πik/3}|1⟩)`, `k = 0, 1, 2`. -/
noncomputable def sicQubitState (k : Fin 4) : PureState qubit :=
  qubitSuperposition (Concrete.sicKet k 0) (Concrete.sicKet k 1) (Concrete.sicKet_normSq k)

/-- The uniform (equal-weight) distribution `¼` over the four SIC states — Alice's "equal mixture":
each of the four states carries probability `¼`. -/
noncomputable def sicProb : Fin 4 → ℝ := Function.const _ 4⁻¹

/-- **Nielsen & Chuang, Exercise 12.4: the maximum mutual information is *strictly* less
than one bit.** For *any* measurement `m` (arbitrary finite outcome set `ι`),

`H(X : Y) < log 2`,

where `X` is Alice's uniform choice among the four tetrahedral/SIC states `|Xₓ⟩` and `Y` is
Bob's outcome. As this holds for every `m`, the *maximum over all measurements* of the
accessible information is strictly below one bit — the exact claim of Exercise 12.4.

Entropies are in nats; one bit is `log 2` nats.
-/
theorem mutualInfo_sicQubitState_lt_log_two {ι : Type*} [Fintype ι]
    (m : Measurement ι qubit) :
    Real.mutualInfo (fun xy : Fin 4 × ι =>
        sicProb xy.1 * m.bornProb (sicQubitState xy.1).toState xy.2) < Real.log 2 := sorry

end AxQM
