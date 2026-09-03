/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.DeutschAlgorithm
import AxQM.Basic.API.Beamsplitter
import AxQM.NC.Ch4.Exercise4_17
import AxQM.NC.Ch7.Exercise7_23

/-!
# Nielsen & Chuang, Exercise 7.13 (optical Deutsch–Jozsa quantum circuit)

*(N&C p. 294.)*

Optical Deutsch-Jozsa quantum circuit for single-photon dual-rail states using beamsplitters/phase
shifters/Kerr media.

* `deutschOracleConstZero` — `f ≡ 0` (constant): `U_f = I`.
* `deutschOracleConstOne` — `f ≡ 1` (constant): `U_f = I ⊗ X` (flip the answer rail).
* `deutschOracleIdentity` — `f = id` (balanced): `U_f = CNOT`.
* `deutschOracleNegation` — `f = ¬` (balanced): `U_f = (X ⊗ I) · CNOT · (X ⊗ I)`, the `0`-controlled
  `NOT`.
* `deutschOracleConstZero_isDeutschOracle` — `deutschOracleConstZero_isDeutschOracle` …
  `deutschOracleNegation_isDeutschOracle` — part (1): each of the four gates is the XOR oracle
  `U_f|x, y⟩ = |x, y ⊕ f(x)⟩` for its function `f` (`IsDeutschOracle`), verified against the gate
  truth tables.
* `deutschOracleConstOne_isDeutschOracle`
* `deutschOracleIdentity_isDeutschOracle`
* `deutschOracleNegation_isDeutschOracle` — `deutschOracleConstZero_isDeutschOracle` …
  `deutschOracleNegation_isDeutschOracle` — part (1): each of the four gates is the XOR oracle
  `U_f|x, y⟩ = |x, y ⊕ f(x)⟩` for its function `f` (`IsDeutschOracle`), verified against the gate
  truth tables.
* `deutschOracleIdentity_eq_kerrGate_conj_hadamard` — part (1), the two balanced oracles from the
  Kerr gate: the identity oracle's `CNOT = (I ⊗ H) · K · (I ⊗ H)` (N&C eq. 7.46) with the entangling
  gate the optical Kerr `K = opticalKerrGate 0 0 π` (not a bare `controlledZGate`), and the negation
  oracle that circuit conjugated by query-rail `X` mirrors.
* `deutschOracleNegation_eq_kerrGate_conj_hadamard_mirror` — part (1), the two balanced oracles from
  the Kerr gate: the identity oracle's `CNOT = (I ⊗ H) · K · (I ⊗ H)` (N&C eq. 7.46) with the
  entangling gate the optical Kerr `K = opticalKerrGate 0 0 π` (not a bare `controlledZGate`), and
  the negation oracle that circuit conjugated by query-rail `X` mirrors.
* `opticalHadamardMirror_evolvePure_dualRailZero` — part (2).
* `opticalHadamardMirror_evolvePure_dualRailOne`
* `deutschOracleConstZero_bornProb` — `deutschOracleConstZero_bornProb` …
  `deutschOracleNegation_bornProb` — the outcome: after Deutsch's circuit, measuring the query qubit
  in the computational basis yields `f(0) ⊕ f(1)` with probability `1` — `0` for the two constant
  oracles, `1` for the two balanced oracles.
* `deutschOracleConstOne_bornProb`
* `deutschOracleIdentity_bornProb`
* `deutschOracleNegation_bornProb` — `deutschOracleConstZero_bornProb` …
  `deutschOracleNegation_bornProb` — the outcome: after Deutsch's circuit, measuring the query qubit
  in the computational basis yields `f(0) ⊕ f(1)` with probability `1` — `0` for the two constant
  oracles, `1` for the two balanced oracles.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The four optical oracles (Exercise 7.13, part 1) -/

/-- **Constant `f ≡ 0`, `U_f = I`.** The oracle that leaves both rails untouched. -/
def deutschOracleConstZero : Evolution (qubit ⊗ qubit) := Evolution.id

/-- **Constant `f ≡ 1`, `U_f = I ⊗ X`.** The oracle that flips the answer rail unconditionally
(an `X` on the second qubit, realised by a fully-reflecting beamsplitter / mirror). -/
def deutschOracleConstOne : Evolution (qubit ⊗ qubit) := pauliXGate.onRight qubit

/-- **Balanced `f = id`, `U_f = CNOT`.** The controlled-`NOT`, realised optically from the Kerr /
Fredkin controlled-`Z` and two Hadamards. -/
def deutschOracleIdentity : Evolution (qubit ⊗ qubit) := cnotGate

/-- **Balanced `f = ¬`, `U_f = (X ⊗ I) · CNOT · (X ⊗ I)`.** The `0`-controlled `NOT`: `CNOT`
conjugated by an `X` on the query rail, so the answer rail flips exactly when the query is `|0⟩`. -/
def deutschOracleNegation : Evolution (qubit ⊗ qubit) :=
  (pauliXGate.onLeft qubit).comp (cnotGate.comp (pauliXGate.onLeft qubit))

/-! ### Each gate is the oracle for its function (Exercise 7.13, part 1) -/

/-- `U_f = I` is the oracle for the constant function `f ≡ 0`: it maps `|x, y⟩` to `|x, y ⊕ 0⟩`. -/
theorem deutschOracleConstZero_isDeutschOracle :
    IsDeutschOracle (fun _ => 0) deutschOracleConstZero := sorry

/-- `U_f = I ⊗ X` is the oracle for the constant function `f ≡ 1`. -/
theorem deutschOracleConstOne_isDeutschOracle :
    IsDeutschOracle (fun _ => 1) deutschOracleConstOne := sorry

/-- `U_f = CNOT` is the oracle for the identity function `f = id`. -/
theorem deutschOracleIdentity_isDeutschOracle :
    IsDeutschOracle id deutschOracleIdentity := sorry

/-- `U_f = (X ⊗ I) · CNOT · (X ⊗ I)` is the oracle for the negation `f = ¬` (`f x = x ⊕ 1`): the
two `X`s on the query rail turn `CNOT` into a `0`-controlled `NOT`, mapping `|x, y⟩` to
`|x, y ⊕ (x ⊕ 1)⟩`. -/
theorem deutschOracleNegation_isDeutschOracle :
    IsDeutschOracle (fun x => x + 1) deutschOracleNegation := sorry

/-! ### Optical construction of the balanced oracles from the Kerr gate (Exercise 7.13, part 1) -/

/-- **Part (1), the identity oracle from a Kerr gate (N&C eq. 7.46).** The balanced oracle `f = id`
is `CNOT = (I ⊗ H) · K · (I ⊗ H)`, where `K = opticalKerrGate 0 0 π` is the optical **Kerr**
controlled-`Z` and each `H` is the algorithm's single-qubit Hadamard (realised optically by a
beamsplitter with phase shifters, N&C p. 294). -/
theorem deutschOracleIdentity_eq_kerrGate_conj_hadamard :
    deutschOracleIdentity
      = (hadamardGate.onRight qubit).comp
          ((opticalKerrGate 0 0 Real.pi).comp (hadamardGate.onRight qubit)) := sorry

/-- **Part (1), the negation oracle from a Kerr gate and mirrors.** The balanced oracle `f = ¬` is
the `0`-controlled `NOT`. -/
theorem deutschOracleNegation_eq_kerrGate_conj_hadamard_mirror :
    deutschOracleNegation
      = (pauliXGate.onLeft qubit).comp
          ((hadamardGate.onRight qubit).comp
            ((opticalKerrGate 0 0 Real.pi).comp
              ((hadamardGate.onRight qubit).comp (pauliXGate.onLeft qubit)))) := sorry

/-! ### Part (2): why no phase shifters are necessary

The only element of the construction that might seem to need a phase shifter is the single-qubit
Hadamard: Exercise 7.9 realises it as `B(π/4) ∘ (1 ⊗ P(π))`, a beamsplitter after a `π` phase
shifter. But the Hadamard can equally be built from a beamsplitter and a **mirror** — the mode
`SWAP` (`Evolution.swap`) that each dual-rail qubit already needs for its `X` gate (the oracles'
answer-rail flip and the negation oracle's query-rail flip are mirrors). Replacing the `π` phase
shifter by that mirror gives `opticalHadamardMirror = SWAP ∘ B(π/4)`, which realises the Hadamard
*exactly* — with **no** residual global phase. So every gate in the four `U_f` (identities,
mirrors, the Kerr controlled-`Z`, and the Hadamards) is a beamsplitter, a mirror, or a Kerr
medium: no phase shifter is necessary. -/

/-- **Part (2), the phase-shifter-free Hadamard on `|0_L⟩ = |01⟩`.** The mirror Hadamard — a
balanced beamsplitter followed by a mirror (mode `SWAP`), *no phase shifter* — sends `|01⟩` to
`(|01⟩ + |10⟩)/√2`, N&C's exact Hadamard action `|01⟩ → (|01⟩ + |10⟩)/√2` with no
global phase. This is why no phase shifter is needed. -/
theorem opticalHadamardMirror_evolvePure_dualRailZero :
    opticalHadamardMirror.evolvePure dualRailZero
      = dualRail ((Real.sqrt 2 : ℂ) / 2) ((Real.sqrt 2 : ℂ) / 2)
          (by simpa using opticalHadamardMirror_amplitudes_normalized 1 0 (by norm_num)) := sorry

/-- **Part (2), the phase-shifter-free Hadamard on `|1_L⟩ = |10⟩`.** The mirror Hadamard sends
`|10⟩` to `(|01⟩ - |10⟩)/√2`, N&C's exact Hadamard action `|10⟩ → (|01⟩ - |10⟩)/√2`
with no global phase — again with only a beamsplitter and a mirror, no phase shifter. -/
theorem opticalHadamardMirror_evolvePure_dualRailOne :
    opticalHadamardMirror.evolvePure dualRailOne
      = dualRail ((Real.sqrt 2 : ℂ) / 2) (-((Real.sqrt 2 : ℂ) / 2))
          (by simpa using opticalHadamardMirror_amplitudes_normalized 0 1 (by norm_num)) := sorry

/-! ### The measured outcome: constant reads `0`, balanced reads `1` -/

/-- **Constant `f ≡ 0` (`U_f = I`) reads `0`** with probability `1` — reports "constant". -/
theorem deutschOracleConstZero_bornProb :
    (controlMeasurement qubit).bornProb
        ((deutschCircuit deutschOracleConstZero).evolvePure (qubitBasis 0 ⊗ qubitBasis 1)).toState 0
      = 1 := sorry

/-- **Constant `f ≡ 1` (`U_f = I ⊗ X`) reads `0`** with probability `1` — reports "constant". -/
theorem deutschOracleConstOne_bornProb :
    (controlMeasurement qubit).bornProb
        ((deutschCircuit deutschOracleConstOne).evolvePure (qubitBasis 0 ⊗ qubitBasis 1)).toState 0
      = 1 := sorry

/-- **Balanced `f = id` (`U_f = CNOT`) reads `1`** with probability `1` — reports "balanced". -/
theorem deutschOracleIdentity_bornProb :
    (controlMeasurement qubit).bornProb
        ((deutschCircuit deutschOracleIdentity).evolvePure (qubitBasis 0 ⊗ qubitBasis 1)).toState 1
      = 1 := sorry

/-- **Balanced `f = ¬` (`0`-controlled `NOT`) reads `1`** with probability `1` — "balanced". -/
theorem deutschOracleNegation_bornProb :
    (controlMeasurement qubit).bornProb
        ((deutschCircuit deutschOracleNegation).evolvePure (qubitBasis 0 ⊗ qubitBasis 1)).toState 1
      = 1 := sorry

end AxQM
