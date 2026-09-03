/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.EigenspaceCollapse
import AxQM.Basic.API.InvolutiveObservable
import AxQM.Concrete.FiveQubitCode
import AxQM.Concrete.NineQubitCode

/-!
# Nielsen & Chuang, Exercise 10.60 — syndrome-measuring circuits for the nine and five qubit codes

*(N&C p. 474.)*

Construct a syndrome-measuring circuit (like Fig 10.16) for the nine and five qubit codes.

* `syndromeMeasureCircuit` — the one-generator block of Figure 10.13.
* `shorSyndromeCircuit`, `shorSyndromeCircuit_measures` — the nine-qubit Shor code (eight
  generators, Figure 10.11).
* `fiveSyndromeCircuit`, `fiveSyndromeCircuit_measures` — the five-qubit code (four generators,
  Figure 10.12).
-/

open scoped Matrix

namespace AxQM

variable {n : ℕ}

/-- **The one-generator syndrome-measuring block** (Figure 10.13, the building block of Figure
10.16) for an honest Pauli-string generator `g : Fin n → Fin 4`: the operator-measurement circuit
`measureObservableCircuit (P_g) = (H ⊗ 1) · C(P_g) · (H ⊗ 1)` on `qubit ⊗ qudit (2ⁿ)`, with the
generator `P_g = pauliStringHamiltonian g 1` promoted to a controllable unitary via its involutivity
`(P_g)² = I`. Stacking one such block, on its own ancilla, per generator of a stabilizer code gives
the code's syndrome-measuring circuit. -/
noncomputable def syndromeMeasureCircuit (g : Fin n → Fin 4) :
    Evolution (qubit.compose (qudit (2 ^ n))) :=
  measureObservableCircuit ((pauliStringHamiltonian g 1).toEvolution
    (pauliStringHamiltonian_op_mul_self g))

/-! ### The nine-qubit Shor code (Figure 10.11 generators) -/

/-- **The nine-qubit Shor code syndrome-measuring circuit**, `Fin 8 → Evolution (qubit ⊗ qudit
512)`: one block per Figure-10.11 generator (`Concrete.shorGenIdx`) — six `Z`-type bit-flip
checks and two `X`-type phase-flip checks, on eight ancillas. This is the Figure-10.16 analogue for
the Shor code. -/
noncomputable def shorSyndromeCircuit (i : Fin 8) :
    Evolution (qubit.compose (qudit (2 ^ 9))) :=
  syndromeMeasureCircuit (Concrete.shorGenIdx i)

/-- **Each Shor-code block measures its generator.** Block `i` records the eigenvalue `(−1)ᵇ` of the
`i`-th Figure-10.11 generator as its ancilla's syndrome bit `b`. -/
theorem shorSyndromeCircuit_measures (i : Fin 8) (ψ : PureState (qudit (2 ^ 9))) (b : Fin 2)
    (hψ : (pauliStringHamiltonian (Concrete.shorGenIdx i) 1).HasEigenstate ((-1 : ℝ) ^ (b : ℕ)) ψ) :
    (shorSyndromeCircuit i).evolvePure ((qubitBasis 0).tmul ψ) = (qubitBasis b).tmul ψ := sorry

/-! ### The five-qubit code (Figure 10.12 generators) -/

/-- **The five-qubit code syndrome-measuring circuit**, `Fin 4 → Evolution (qubit ⊗ qudit 32)`: one
Figure-10.13 block per Figure-10.12 generator (`Concrete.fiveQubitGenIdx`, the four cyclic
`XZZXI`-type generators), on four ancillas. This is the Figure-10.16 analogue for the five-qubit
code. -/
noncomputable def fiveSyndromeCircuit (i : Fin 4) :
    Evolution (qubit.compose (qudit (2 ^ 5))) :=
  syndromeMeasureCircuit (Concrete.fiveQubitGenIdx i)

/-- **Each five-qubit-code block measures its generator.** Block `i` records the eigenvalue `(−1)ᵇ`
of the `i`-th Figure-10.12 generator as its ancilla's syndrome bit `b`. -/
theorem fiveSyndromeCircuit_measures (i : Fin 4) (ψ : PureState (qudit (2 ^ 5))) (b : Fin 2)
    (hψ : (pauliStringHamiltonian (Concrete.fiveQubitGenIdx i) 1).HasEigenstate
      ((-1 : ℝ) ^ (b : ℕ)) ψ) :
    (fiveSyndromeCircuit i).evolvePure ((qubitBasis 0).tmul ψ) = (qubitBasis b).tmul ψ := sorry

end AxQM
