/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.BlochRotationGate
import AxQM.Basic.API.BlochState
import AxQM.Basic.API.MaximallyMixed
import AxQM.Basic.API.QuantumChannel
import AxQM.Basic.API.Qudit
import AxQM.Basic.API.RandomUnitaryChannel
import AxQM.Basic.API.UnitaryBlochRotation
import AxQM.Concrete.BlochAffineDecomposition
import AxQM.Concrete.BlochMatrix
import AxQM.Concrete.BlochRotation
import AxQM.NC.Ch2.Exercise2_72
import AxQM.ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM
import AxQM.ToMathlib.Analysis.InnerProductSpace.EuclideanConjVec
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSumTheorem
import AxQM.ToMathlib.Analysis.Matrix.SVD
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Nielsen & Chuang, Problem 8.3 (Random unitary channels)

*(N&C p. 396.)*

Show all unital channels are random-unitary averages for single qubits but not for larger systems.

* `pauliChannelUnitary` — the four Pauli conjugations as `Evolution`s of the qubit, realised as `I`
  and the `π`-rotations `R_x̂(π), R_ŷ(π), R_ẑ(π)` (which equal `X, Y, Z` up to a global phase that
  cancels in the conjugation `U ρ U†`, so this *is* the Pauli channel).
* `pauliChannel` — the Pauli channel `∑ₖ pₖ σₖ ρ σₖ` as a `RandomUnitaryChannel`.
* `isRandomUnitary_of_isChannel_isUnital` — the qubit converse of Problem 8.3: every unital qubit
  channel is random-unitary, `IsChannel f → IsUnital f → IsRandomUnitary f`.
* `exists_unital_channel_not_isRandomUnitary` — a *unital channel that is not random-unitary*
  exists.
-/

open scoped InnerProductSpace ComplexOrder Matrix

noncomputable section

namespace AxQM

/-- **The four Pauli conjugations of the qubit, as unitary `Evolution`s.** Index `k : Fin 4` selects
`I, X, Y, Z`, realised as the identity and the axis `π`-rotations `R_x̂(π), R_ŷ(π), R_ẑ(π)`.
Since `R_n̂(π) = −i (n̂·σ)`, conjugation `R_n̂(π) ρ R_n̂(π)†` equals the Pauli conjugation `σ ρ
σ` (the global phase `−i` cancels), so mixing these is the **Pauli channel** `∑ₖ pₖ σₖ ρ σₖ`. -/
def pauliChannelUnitary : Fin 4 → Evolution qubit
  | 0 => rotAxisGate ![1, 0, 0] 0
  | 1 => rotAxisGate ![1, 0, 0] Real.pi
  | 2 => rotAxisGate ![0, 1, 0] Real.pi
  | 3 => rotAxisGate ![0, 0, 1] Real.pi

/-- **The qubit Pauli channel** `E(ρ) = ∑ₖ pₖ σₖ ρ σₖ` as a `RandomUnitaryChannel`, for a
probability distribution `p : Fin 4 → ℝ` over the four Paulis (`pₖ ≥ 0`, `∑ pₖ = 1`). Its unitaries
are `pauliChannelUnitary`. This is the running family of unital, random-unitary qubit channels of
Problem 8.3. -/
def pauliChannel (p : Fin 4 → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) :
    RandomUnitaryChannel qubit where
  card := 4
  prob := p
  unitary := pauliChannelUnitary
  prob_nonneg := hp0
  sum_prob := hp

/-! ### The qubit converse of Problem 8.3 — *every* unital qubit channel is random-unitary

For a single qubit, unitality really does force the random-unitary form `E(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†` on
a channel — the "tempting belief" is *true* in dimension two (Landau & Streater). -/

/-- **Problem 8.3, qubit converse (dimension two): every unital qubit channel is random-unitary.**
A CPTP quantum channel `f` of the `qubit` (`IsChannel`) that is **unital** (`IsUnital`, `f (I/2) =
I/2`) is a **random-unitary** (mixed-unitary) channel `f (ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†` (`IsRandomUnitary`).
This is the direction of Nielsen & Chuang, Problem 8.3 that *holds*: for one qubit the tempting
belief is correct.
-/
theorem isRandomUnitary_of_isChannel_isUnital {f : State qubit → State qubit}
    (hf : IsChannel f) (hu : IsUnital f) : IsRandomUnitary f := sorry

/-! ### The counterexample in dimension `≥ 3` — *not* every unital channel is random-unitary

The "tempting belief" *fails* for systems larger than a qubit: some unital CPTP channel admits no
random-unitary representation. -/

/-- **Problem 8.3, the larger-system direction.** Not every unital channel is a
random-unitary average once the system is larger than a single qubit (Landau & Streater).
-/
theorem exists_unital_channel_not_isRandomUnitary :
    ∃ f : State (qudit 3) → State (qudit 3), IsChannel f ∧ IsUnital f ∧ ¬ IsRandomUnitary f := sorry

end AxQM
