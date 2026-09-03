/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Exercise10_60
import AxQM.Concrete.StabilizerCodeDimension
import AxQM.Basic.API.PauliTrotter
import AxQM.Basic.API.Eigenstate
import AxQM.Basic.API.PureState

/-!
# Nielsen & Chuang, Exercise 10.74 — fault-tolerant preparation of the five-qubit code encoded |0⟩

*(N&C p. 493.)*

Construct a quantum circuit to fault-tolerantly generate the encoded |0> for the five qubit code.

* `IsFiveEncodedZero` — the stabilizer definition of the encoded `|0⟩`: a `+1`-eigenstate of all
  five operators.
* `fiveEncodedZeroPrep` — the encoded-`|0⟩` preparation circuit, `Fin 5 → Evolution`: one
  measurement block per operator of `Concrete.fiveQubitZeroGenIdx`.
* `fiveEncodedZeroPrep_measures` — each block measures its operator: block `i` records the
  eigenvalue `(−1)ᵇ` of the `i`-th operator (a generator, or `Z̄` for `i = 4`) as its ancilla bit
  `b`, leaving the register in the eigenstate (Figure 10.13 working as described).
* `fiveEncodedZeroPrep_stabilized_zero` — on the encoded `|0⟩` every block reads `0`: an
  `IsFiveEncodedZero` state is left invariant with the all-zero syndrome, confirming successful
  preparation.
* `fiveEncodedZero_exists` — the construction prepares a state (existence): there is an
  `IsFiveEncodedZero` state, so the circuit's target is nonempty.
* `fiveEncodedZero_unique` — it prepares exactly the encoded `|0⟩` (uniqueness): any two
  `IsFiveEncodedZero` states are equal up to a global phase (`ψ.toState = φ.toState`), so the five
  measurements pin the prepared state to a single codeword.
-/

namespace AxQM

/-- **The five-qubit code encoded `|0⟩` (stabilizer definition).** A pure state `ψ` on the
five-qubit register `qudit (2⁵)` is the encoded `|0⟩` when it is a simultaneous `+1`-eigenstate
of all five operators of `Concrete.fiveQubitZeroGenIdx` — the four Figure-10.12 stabilizer
generators `g₁,…,g₄` **and** the logical `Z̄ = Z⊗Z⊗Z⊗Z⊗Z`. -/
def IsFiveEncodedZero (ψ : PureState (qudit (2 ^ 5))) : Prop :=
  ∀ i : Fin 5, (pauliStringHamiltonian (Concrete.fiveQubitZeroGenIdx i) 1).HasEigenstate 1 ψ

/-- **The five-qubit code encoded-`|0⟩` preparation circuit**, `Fin 5 → Evolution (qubit ⊗ qudit
32)`: one Figure-10.13 measurement block (`syndromeMeasureCircuit`) per operator of
`Concrete.fiveQubitZeroGenIdx` — the four stabilizer generators (blocks `0,…,3`) plus a fifth block
measuring the logical `Z̄ = Z⊗⁵`. Measuring all five commuting operators and fixing the signs lands
in the encoded `|0⟩`; fault tolerance comes from realising each block's measurement with a verified
cat-state ancilla. -/
noncomputable def fiveEncodedZeroPrep (i : Fin 5) :
    Evolution (qubit.compose (qudit (2 ^ 5))) :=
  syndromeMeasureCircuit (Concrete.fiveQubitZeroGenIdx i)

/-- **Each block measures its operator.** Block `i` records the eigenvalue `(−1)ᵇ` of the `i`-th
operator of `Concrete.fiveQubitZeroGenIdx` (a stabilizer generator, or the logical `Z̄` for
`i = 4`) as its ancilla's measurement bit `b`, leaving the register in the eigenstate `ψ`. -/
theorem fiveEncodedZeroPrep_measures (i : Fin 5) (ψ : PureState (qudit (2 ^ 5))) (b : Fin 2)
    (hψ : (pauliStringHamiltonian (Concrete.fiveQubitZeroGenIdx i) 1).HasEigenstate
      ((-1 : ℝ) ^ (b : ℕ)) ψ) :
    (fiveEncodedZeroPrep i).evolvePure ((qubitBasis 0).tmul ψ) = (qubitBasis b).tmul ψ := sorry

/-- **The encoded `|0⟩` gives the all-zero syndrome.** An encoded-`|0⟩` state `ψ`
(`IsFiveEncodedZero`: a `+1`-eigenstate of every generator and of `Z̄`) is left invariant by every
block of the preparation circuit, each ancilla reading `0`: the circuit verifies the encoded
`|0⟩`. -/
theorem fiveEncodedZeroPrep_stabilized_zero (ψ : PureState (qudit (2 ^ 5)))
    (hψ : IsFiveEncodedZero ψ) (i : Fin 5) :
    (fiveEncodedZeroPrep i).evolvePure ((qubitBasis 0).tmul ψ) = (qubitBasis 0).tmul ψ := sorry

/-- **The construction prepares a state (existence).** There **is** an encoded-`|0⟩` state.
Physically, the five-block circuit `fiveEncodedZeroPrep` — measuring the four stabilizer
generators and the logical `Z̄` and fixing every sign to `+1` — has a nonempty target: its joint
`+1`-eigenspace is nonzero.
-/
theorem fiveEncodedZero_exists : ∃ ψ, IsFiveEncodedZero ψ := sorry

/-- **The construction prepares exactly the encoded `|0⟩` (uniqueness).** Any two encoded-`|0⟩`
states `ψ`, `φ` (each `IsFiveEncodedZero`: a common `+1`-eigenstate of all five operators
`⟨g₁,…,g₄, Z̄⟩`) have the same density operator, `ψ.toState = φ.toState` — they are equal up to
a global phase. So post-selecting the all-`+1` outcome of the five measurements pins the
prepared state down to a *single* encoded `|0⟩`.
-/
theorem fiveEncodedZero_unique {ψ φ : PureState (qudit (2 ^ 5))}
    (hψ : IsFiveEncodedZero ψ) (hφ : IsFiveEncodedZero φ) :
    ψ.toState = φ.toState := sorry

end AxQM
