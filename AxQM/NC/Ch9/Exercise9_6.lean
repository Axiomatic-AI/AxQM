/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochMatrix
import AxQM.ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM
import AxQM.ToMathlib.Analysis.InnerProductSpace.TraceNorm
import AxQM.Basic.API.BlochState
import AxQM.Basic.API.TraceDistance
import AxQM.Basic.API.Mixture
import AxQM.NC.Ch2.Exercise2_72
import AxQM.NC.Ch4.Exercise4_1

/-!
# Nielsen & Chuang, Exercise 9.6 (Trace distance between qubit density operators)

*(N&C p. 403.)*

Compute trace distance between given qubit density operators.

* `qubitMix34Zero` — the state `¾|0⟩⟨0| + ¼|1⟩⟨1|`.
* `qubitMix23Zero` — the state `⅔|0⟩⟨0| + ⅓|1⟩⟨1|`.
* `qubitMix23Plus` — the state `⅔|+⟩⟨+| + ⅓|−⟩⟨−|`.
* `traceDistance_qubitMix_zBasis` — part (a): `D(ρ, σ) = 1/12`.
* `traceDistance_qubitMix_xBasis` — part (b): `D(ρ, σ') = √13/12`.
-/

open Matrix ContinuousLinearMap

noncomputable section

namespace AxQM

/-- The textbook state `ρ = ¾|0⟩⟨0| + ¼|1⟩⟨1|`, as a mixture of the computational basis
projectors. -/
def qubitMix34Zero : State qubit :=
  State.mix ![3/4, 1/4] (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) ![qubitKet0.toState, (qubitBasis 1).toState]

/-- The textbook state `σ = ⅔|0⟩⟨0| + ⅓|1⟩⟨1|`, as a mixture of the computational basis
projectors. -/
def qubitMix23Zero : State qubit :=
  State.mix ![2/3, 1/3] (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) ![qubitKet0.toState, (qubitBasis 1).toState]

/-- The textbook state `σ' = ⅔|+⟩⟨+| + ⅓|−⟩⟨−|`, as a mixture of the Hadamard basis
projectors. -/
def qubitMix23Plus : State qubit :=
  State.mix ![2/3, 1/3] (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) ![qubitPlus.toState, qubitMinus.toState]

/-- **Exercise 9.6, part (a).** The trace distance between `ρ = ¾|0⟩⟨0| + ¼|1⟩⟨1|` and
`σ = ⅔|0⟩⟨0| + ⅓|1⟩⟨1|` is `1/12`. -/
theorem traceDistance_qubitMix_zBasis :
    qubitMix34Zero.traceDistance qubitMix23Zero = 1 / 12 := sorry

/-- **Exercise 9.6, part (b).** The trace distance between `ρ = ¾|0⟩⟨0| + ¼|1⟩⟨1|` and
`σ' = ⅔|+⟩⟨+| + ⅓|−⟩⟨−|` is `√13/12`. -/
theorem traceDistance_qubitMix_xBasis :
    qubitMix34Zero.traceDistance qubitMix23Plus = Real.sqrt 13 / 12 := sorry

end AxQM
