/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.CnotFanEvolution
import AxQM.Basic.API.FourGateReachableWire
import AxQM.Concrete.PauliNormalizerGenerators
import AxQM.Concrete.PauliStringDiagonalize
import AxQM.Concrete.SingleQubitWire
import AxQM.Concrete.Rotation
import AxQM.Basic.API.PauliDiagWire
import AxQM.Basic.API.InvolutiveObservable

/-!
# The Figure-4.19 circuit for a Trotter summand, and its faithfulness (N&C Problem 4.3(3))

Nielsen & Chuang **Problem 4.3(3)** asks to implement the Trotter summand `exp(-i h_g g Δ)` — the
unit-`ℏ` propagator `exp(-i c t · g)` of a single Pauli-string Hamiltonian `c · g` — with `O(n)`
one- and two-qubit gates. The construction is the compute–rotate–uncompute cascade of Figure
4.19 (N&C §4.7.3):

## Main declarations
* `pauliStringExpCircuit n g c ts θ` — the Figure-4.19 circuit `B · V† · R_z · V · B†` as one
  `Evolution (qudit (2ⁿ))` (the `V†`/`B†` uncomputation are the `Evolution` adjoints of the fan and
  the basis-change layer). Here `c` is the collector wire, `ts` the remaining support wires (so the
  support of `g` is `insert c ts`), and `θ` the collector-rotation angle.

* `pauliStringExpCircuit_op_eq_propagator` — **faithfulness**: taking `θ = 2 c t`, the
  circuit's operator equals the Trotter summand `((pauliStringHamiltonian g c).propagator 1 0 t).op
  = exp(-i c t · g)`. So `pauliStringExpCircuit n g c ts (2 c t)` implements `exp(-i h_g g Δ)` for
  `c = h_g`, `t = Δ` — the operator Problem 4.3(3) asks to realise.
-/

open Matrix
open scoped InnerProductSpace
-- The `L∞` operator norm supplies the `NormedRing`/`NormedAlgebra ℂ (Matrix …)` instances that
-- `NormedSpace.exp_smul_mul_I_of_mul_self_eq_one` needs to collapse the bit-string exponential to a
-- rotation; the resulting matrix `exp` is norm-independent (this only enables the lemma).
open scoped Matrix.Norms.Operator

namespace AxQM

noncomputable section

open AxQM.Concrete

/-- **The Nielsen–Chuang Figure-4.19 circuit for a Pauli-string Trotter summand.** The
compute–rotate–uncompute cascade `B · V† · R_z(θ) · V · B†` implementing `exp(-i c t · g)` (for
`θ = 2 c t`), as one `Evolution (qudit (2ⁿ))`:

* `B = pauliDiagLayer n g` — the layer of single-qubit basis-change gates diagonalising each Pauli
  factor of `g` to `Z`; `B†` its adjoint;
* `V = cnotFanIntoEvolution n c ts` — the `CNOT` fan computing the support parity onto the collector
  wire `c` (controls `ts`); `V†` its adjoint (the uncomputation);
* `R_z(θ) = rotZWireEvolution n c θ` — the single-qubit `z`-rotation on the collector.

Reading the product right-to-left (the order gates act on a state): apply `B†`, then the parity fan
`V`, then the collector rotation, then uncompute the fan `V†`, then `B`. For a Pauli string whose
support is `insert c ts`, this realises `exp(-i c t · g)` (`pauliStringExpCircuit_op_eq_propagator`)
using `O(n)` elementary gates. -/
def pauliStringExpCircuit (n : ℕ) (g : Fin n → Fin 4) (c : Fin n) (ts : List (Fin n)) (θ : ℝ) :
    Evolution (qudit (2 ^ n)) :=
  pauliDiagLayer n g
    * (cnotFanIntoEvolution n c ts).adjoint
    * rotZWireEvolution n c θ
    * cnotFanIntoEvolution n c ts
    * (pauliDiagLayer n g).adjoint

/-- **Problem 4.3(3), faithfulness of the circuit.**

`(pauliStringExpCircuit n g c ts (2 c t)).op = ((pauliStringHamiltonian g c).propagator 1 0
t).op`,

i.e. `exp(-i c t · g)`. So the circuit realises the operator `exp(-i h_g g Δ)` of Problem 4.3(3)
for `c = h_g`, `t = Δ = 1/k`.
-/
theorem pauliStringExpCircuit_op_eq_propagator {n : ℕ} (g : Fin n → Fin 4) (c : Fin n)
    (ts : List (Fin n)) (hc : c ∉ ts) (hnd : ts.Nodup) (hgc : g c ≠ 0) (hgts : ∀ t ∈ ts, g t ≠ 0)
    (hrest : ∀ k, k ≠ c → k ∉ ts → g k = 0) (coeff t : ℝ) :
    (pauliStringExpCircuit n g c ts (2 * coeff * t)).op
      = ((pauliStringHamiltonian g coeff).propagator 1 0 t).op := sorry

end

end AxQM
