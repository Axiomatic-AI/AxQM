/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerSimulationCost
import AxQM.Concrete.PauliStringCliffordCircuit
import AxQM.Concrete.StabilizerCodeDimension
import AxQM.Concrete.StabilizerGeneratorFlip
import AxQM.Concrete.PauliStringEncodingLayers
import AxQM.Concrete.PauliNormalizerGenerators

/-!
# Concrete: the stabiliser tableau simulator and its unitary-fragment correctness

The **correctness of the classical stabiliser simulator** underlying the Gottesman–Knill theorem
(Nielsen & Chuang **Theorem 10.7**, §10.5.4, p. 464), for the *unitary fragment* of a stabiliser
computation.
-/

open scoped Matrix

namespace AxQM.Concrete

noncomputable section

variable {n : ℕ}

/-- The **all-zeros computational-basis vector** `|0…0⟩` on the `n`-qubit register, as a raw vector
`(Fin n → Fin 2) → ℂ`: the standard basis vector `Pi.single 0 1` supported at the all-zeros bit
string. -/
def compBasisZero (n : ℕ) : (Fin n → Fin 2) → ℂ := Pi.single 0 1

/-- A **stabiliser tableau** on the `n`-qubit register: the classical description the
Gottesman–Knill simulator tracks — `n` generators `gen i` (each a Pauli string `Fin n → Fin 4`),
together with the `±1` sign `sign i` of each. It represents the signed generator family
`(sign i • pauliString (gen i))ᵢ`. -/
structure StabilizerTableau (n : ℕ) where
  /-- The `n` generators, each a phase-free Pauli string (a check-matrix row). -/
  gen : Fin n → Fin n → Fin 4
  /-- The `±1` sign carried by each generator. -/
  sign : Fin n → ℂ

/-- The tableau **stabilises** the vector `v` when every signed generator fixes it:
`(sign i • pauliString (gen i)) ·ᵥ v = v` for all `i`. This is the simulator's correctness
invariant — "the tracked generators are a genuine stabiliser of the state". -/
def StabilizerTableau.Stabilizes (T : StabilizerTableau n) (v : (Fin n → Fin 2) → ℂ) : Prop :=
  ∀ i, (T.sign i • pauliString (T.gen i)).mulVec v = v

/-- The **trivial preparation tableau** `⟨Z₁, …, Zₙ⟩`: generator `i` is the pure-`Z` string `Zᵢ`
(`zGenPauli i`) with sign `+1`. -/
def StabilizerTableau.prep (n : ℕ) : StabilizerTableau n where
  gen := zGenPauli
  sign := fun _ => 1

/-- Whether a stabiliser operation is a **measurement** (`measure p`). -/
def StabilizerOp.IsMeasurement : StabilizerOp n → Prop
  | .measure _ => True
  | _ => False

/-- The **actual raw-state evolution** of one stabiliser operation on the `n`-qubit register:
`prep` prepares `|0…0⟩`, a Clifford / Pauli gate applies its unitary matrix, and `measure` carries
the state through unchanged (its Born-rule collapse is the physics engine of §10.5.3). -/
def StabilizerOp.stepState : StabilizerOp n → ((Fin n → Fin 2) → ℂ) → ((Fin n → Fin 2) → ℂ)
  | .prep, _ => compBasisZero n
  | .clifford g, v => g.toMatrix.mulVec v
  | .pauli p, v => (pauliString p).mulVec v
  | .measure _, v => v

/-- The **classical tableau update** of one stabiliser operation — the Gottesman–Knill simulator's
per-operation step. -/
def StabilizerOp.stepTableau : StabilizerOp n → StabilizerTableau n → StabilizerTableau n
  | .prep, _ => StabilizerTableau.prep n
  | .clifford g, T => ⟨fun i => g.act (T.gen i), fun i => T.sign i * g.sign (T.gen i)⟩
  | .pauli p, T => ⟨T.gen, fun i => T.sign i * (-1) ^ pauliAnticommCount p (T.gen i)⟩
  | .measure _, T => T

/-- The **tableau run** of a stabiliser computation: fold the per-operation classical update
`StabilizerOp.stepTableau` over the operation list, left to right (first operation first). -/
def StabilizerTableau.run : StabilizerComputation n → StabilizerTableau n → StabilizerTableau n
  | [], T => T
  | op :: rest, T => StabilizerTableau.run rest (op.stepTableau T)

/-- The **actual state** after running a stabiliser computation: fold the raw-state evolution
`StabilizerOp.stepState` over the operation list, left to right. -/
def runState : StabilizerComputation n → ((Fin n → Fin 2) → ℂ) → ((Fin n → Fin 2) → ℂ)
  | [], v => v
  | op :: rest, v => runState rest (op.stepState v)

/-- **The stabiliser simulator is correct on the unitary fragment (N&C Theorem 10.7).** For a
**measurement-free** stabiliser computation `prog` (state preparations and Hadamard / phase /
controlled-`NOT` / Pauli gates), if the tableau `T` stabilises the state `v`, then after running
the computation the tracked tableau `StabilizerTableau.run prog T` stabilises the
actually-evolved state `runState prog v`.
-/
theorem StabilizerTableau.run_stabilizes :
    ∀ (prog : StabilizerComputation n), (∀ op ∈ prog, ¬ op.IsMeasurement) →
      ∀ (T : StabilizerTableau n) (v : (Fin n → Fin 2) → ℂ),
        T.Stabilizes v → (StabilizerTableau.run prog T).Stabilizes (runState prog v) := sorry

end

end AxQM.Concrete
