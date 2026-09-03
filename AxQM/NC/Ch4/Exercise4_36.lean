/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.QuditPairPermGate
import AxQM.Concrete.ModularAdder

/-!
# Nielsen & Chuang, Exercise 4.36 — a circuit adding two two-bit numbers modulo 4

*(N&C p. 189.)*

Construct a quantum circuit to add two two-bit numbers modulo 4.

* `adderCarryToffoli`
* `adderHighCnot`
* `adderLowCnot`
* `modFourAdderCircuit` — the two-bit ripple-carry adder as a composition of three elementary
  gates — a Toffoli and two CNOTs — on the four-qubit register `qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))`
  whose wires carry `(x₀, y₀, x₁, y₁)`.
* `adderKet`
* `modFourAdderCircuit_evolvePure_adderKet` — the exercise: `modFourAdderCircuit |x, y⟩ = |x, x +
  y⟩` for every pair of two-bit numbers `x, y : Fin 4`, where the second register now holds the
  binary digits of `x + y` computed in `Fin 4`, i.e. modulo `4`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The elementary-gate circuit

The four wires of `qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))` carry `(x₀, y₀, x₁, y₁)` — the low/high bits
of the two input registers, interleaved so the carry lands adjacently. -/

/-- **The carry gate** `Toffoli(x₀, y₀ → y₁)`: on `qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))` it flips the
high `y`-bit (wire `3`) exactly when both `x₀` (wire `0`) and `y₀` (wire `1`) are `|1⟩`, writing the
carry `x₀ ∧ y₀` into `y₁`. -/
def adderCarryToffoli : Evolution (qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))) :=
  controlledUnitary (controlledUnitary (pauliXGate.onRight qubit))

/-- **The high-bit gate** `CNOT(x₁ → y₁)`: the CNOT on the innermost wire pair `(x₁, y₁)` =
`(2, 3)`, adding the high input bit `x₁` into `y₁`. -/
def adderHighCnot : Evolution (qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))) :=
  (cnotGate.onRight qubit).onRight qubit

/-- **The low-bit gate** `CNOT(x₀ → y₀)`: controlled on `x₀` (wire `0`), flips `y₀` (wire `1`),
adding the low input bit `x₀` into `y₀`. -/
def adderLowCnot : Evolution (qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))) :=
  controlledUnitary (pauliXGate.onLeft (qubit ⊗ qubit))

/-- **Exercise 4.36's circuit:** the two-bit modulo-`4` ripple-carry adder as an explicit
elementary-gate circuit on the four-qubit register `qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))` (wires
`x₀, y₀, x₁, y₁`). It is the composition — applied right to left — of the carry `Toffoli(x₀, y₀ →
y₁)`, then `CNOT(x₁ → y₁)`, then `CNOT(x₀ → y₀)`. -/
def modFourAdderCircuit : Evolution (qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))) :=
  adderLowCnot.comp (adderHighCnot.comp adderCarryToffoli)

/-- **The input encoding of two two-bit numbers** `x, y : Fin 4` on the four adder wires: the
computational basis state `|x₀⟩ ⊗ |y₀⟩ ⊗ |x₁⟩ ⊗ |y₁⟩`, where `x₀ = lowBit x`, `x₁ = highBit x`
(and likewise for `y`) are the binary digits. -/
def adderKet (x y : Fin 4) : PureState (qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))) :=
  (qubitBasis (Concrete.lowBit x)) ⊗ ((qubitBasis (Concrete.lowBit y)) ⊗
    ((qubitBasis (Concrete.highBit x)) ⊗ (qubitBasis (Concrete.highBit y))))

/-- **Nielsen & Chuang, Exercise 4.36.** The constructed circuit `modFourAdderCircuit` performs the
transformation `|x, y⟩ → |x, x + y mod 4⟩`: on the encoding `|x⟩|y⟩` of any two two-bit numbers
`x, y : Fin 4` it leaves the first register unchanged and replaces the second by the binary
digits of `x + y` computed in `Fin 4` — that is, modulo `4`. -/
theorem modFourAdderCircuit_evolvePure_adderKet (x y : Fin 4) :
    modFourAdderCircuit.evolvePure (adderKet x y) = adderKet x (x + y) := sorry

end AxQM
