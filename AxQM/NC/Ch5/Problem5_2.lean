/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.AdaptiveMeasurement
import AxQM.Basic.API.Associator
import AxQM.Basic.API.CNOTDensityMatrix
import AxQM.Basic.API.CompositeMeasurement
import AxQM.Basic.API.ControlMeasurementCommute
import AxQM.Basic.API.ControlledControlledUnitary
import AxQM.Basic.API.ControlledPhaseShift
import AxQM.Basic.API.ControlledUnitaryDecomposition
import AxQM.Basic.API.ControlledZ
import AxQM.Basic.API.DeferredMeasurementReindex
import AxQM.Basic.API.Ensemble
import AxQM.Basic.API.Entropy
import AxQM.Basic.API.EntropyComposite
import AxQM.Basic.API.Evolution
import AxQM.Basic.API.HadamardGate
import AxQM.Basic.API.LeftPairGate
import AxQM.Basic.API.MeasureObservable
import AxQM.Basic.API.MeasurementPrecompose
import AxQM.Basic.API.Mixture
import AxQM.Basic.API.MutualInformation
import AxQM.Basic.API.PureMarginalEntropy
import AxQM.Basic.API.Qubit
import AxQM.Basic.API.Qudit
import AxQM.Basic.API.QuditGate
import AxQM.Basic.API.RelativeEntropy
import AxQM.Basic.API.RelativePhase
import AxQM.Basic.API.SchmidtDecomposition
import AxQM.Basic.API.Support
import AxQM.Basic.API.Swap
import AxQM.Basic.API.SystemIsoComm
import AxQM.Basic.API.Teleportation
import AxQM.Basic.API.WirePermutation
import AxQM.Basic.Composite
import AxQM.Basic.Evolution
import AxQM.Basic.Measurement
import AxQM.Basic.PartialTrace
import AxQM.Basic.SystemIso
import AxQM.Concrete.QftGateCircuit
import AxQM.Core.MultiControlledNotBasis
import AxQM.Core.QftRegisterBridge
import AxQM.Core.QftTowerHeadLayer
import AxQM.Core.QtowerMeasurement
import AxQM.Core.QtowerSingleWireGate
import AxQM.Core.QtowerTensorPow
import AxQM.NC.Ch11.StrongSubadditivityGeneral
import AxQM.NC.Ch11.Theorem11_8
import AxQM.NC.Ch2.Exercise2_57
import AxQM.NC.Ch2.Exercise2_78
import AxQM.NC.Ch4.Exercise4_35
import AxQM.ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle
import AxQM.ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
import AxQM.ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum
import AxQM.ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import AxQM.ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import AxQM.ToMathlib.Analysis.InnerProductSpace.ReducedState
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Nielsen & Chuang, Problem 5.2 (the measured quantum Fourier transform)

*(N&C p. 243.)*

Measured QFT: QFT then measurement equals a circuit of only one-qubit gates + measurement with
classical control.

* `qtowerPhaseWireCascade`
* `qftTailBranch`
* `qftTowerEvolution_measure_postMeasurement_eq_towerKet` — Same collapse, up to the swap
  relabelling — the measured QFT collapses at outcome `r` to the recorded state `towerKet n r`
  (`qftTowerEvolution_measure_postMeasurement_eq_towerKet`) and the semiclassical circuit to its
  bit-reversal `towerKet n (fun i => r i.rev)`
  (`semiclassicalMeasuredQft_postMeasurement_eq_towerKet`), independent of the input: the two agree
  exactly up to the `Fin.rev` wire relabelling the Figure 5.1 swap network became once measurement
  is the last step (§4.4 deferred measurement) — no swap *gate* survives.
* `semiclassicalMeasuredQftOutcomeEquiv`
* `semiclassicalMeasuredQft`
* `semiclassicalMeasuredQft_bornProb_eq` — Same outcome statistics —
  `semiclassicalMeasuredQft_bornProb_eq`: for every input `ρ` and outcome `r`, `p(r ∣ measured QFT)
  = p(r ∣ semiclassicalMeasuredQft n)`.
* `semiclassicalMeasuredQft_postMeasurement_eq_towerKet`
* `qftTailBranch_eq_qtowerSingleWire_prod`
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The gate placed on a wire pair of a register `qubit ⊗ (qubit ⊗ R)`

The form the whole-circuit reduction (a later chunk) composes over: control on wire `0`, the phase
gate `P(φ)` on the target wire `1`, and the remaining wires `R` idle. -/

variable {R : QSystem}

variable {S : QSystem}

section MeasuredPhaseWireCascade

/-- The **cascade of single-wire phase gates** on the tower `qtower n qubit`. This is the shape of a
control wire's *deferred* classical-control branch gate. -/
def qtowerPhaseWireCascade (n : ℕ) (gs : List (Fin (n + 1) × ℝ)) : Evolution (qtower n qubit) :=
  (gs.map fun p => Evolution.qtowerSingleWire n p.1 (phaseShiftGate p.2)).prod

end MeasuredPhaseWireCascade

section SwapFreeHeadTmul

/-- The **classically-controlled tail phase cascade** the deferred head control wire leaves on the
tail wires for measured head bit `i`: nothing (`Evolution.id`) on outcome `0`, and the tail phase
cascade `qtowerPhaseWireCascade n (qftHeadRotationList n)` on outcome `1`: a single-wire phase
cascade with classical control on the measured head bit, no gate touching the head wire. This is
the classically-controlled input the outer
induction feeds to the level-`n` QFT on the disentangled tail. -/
def qftTailBranch (n : ℕ) (i : Fin 2) : Evolution (qtower n qubit) :=
  ![Evolution.id, qtowerPhaseWireCascade n (qftHeadRotationList n)] i

end SwapFreeHeadTmul

/-! ### The measured QFT collapses to the recorded computational-basis state (chunk 3b-vii)

The outcome **statistics** of the measured QFT match the semiclassical circuit
(`semiclassicalMeasuredQft_bornProb_eq`, below). The other half of "equivalent as a measurement"
is the **collapsed state**: what state the register is left in for a given outcome.
Here the measured QFT's side of that is settled in closed form — measuring every wire of the tower
in the computational basis after the transported quantum Fourier transform collapses the register to
the **recorded basis state** `towerKet n r`, independent of the input `ρ`:

  `postMeas(qtowerMeasurement n · (qftTowerEvolution n · ρ), r) = (towerKet n r).toState`.
-/

section MeasuredQftCollapse

/-- **Problem 5.2 (the measured QFT collapses to the recorded computational-basis state).** The
state after the transported quantum Fourier transform `qftTowerEvolution n` and *then* the
terminal per-wire computational-basis measurement `qtowerMeasurement n`, at outcome `r`, is
exactly the computational-basis tower state `towerKet n r` — **independent of the input** `ρ`:

`postMeas(qtowerMeasurement n · (qftTowerEvolution n · ρ), r) = (towerKet n r).toState`.

Measuring every wire in the computational basis is a rank-one projective measurement, so it
fully collapses the register onto the recorded bit-string and retains no memory of the
pre-measurement state.
-/
theorem qftTowerEvolution_measure_postMeasurement_eq_towerKet (n : ℕ)
    (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2)
    (hp : (qtowerMeasurement n).bornProb ((qftTowerEvolution n).evolve ρ) r ≠ 0) :
    (qtowerMeasurement n).postMeasurement ((qftTowerEvolution n).evolve ρ) r hp
      = (towerKet n r).toState := sorry

end MeasuredQftCollapse

/-! ### The semiclassical realization of the measured QFT (outer tower induction)

`semiclassicalMeasuredQft n` is manifestly the circuit N&C Problem 5.2 asks for — a circuit of *one*
qubit gates and measurement with classical control, and **no two qubit gate**:

* the single-wire head Hadamard `Evolution.qtowerSingleWire (n+1) 0 hadamardGate`, applied first
  (`Measurement.precompose`);
* the head-wire computational-basis measurement `controlMeasurement (qtower n qubit)`;
* **classical control** (`Measurement.adaptiveCascade`): the measurement of the remaining wires is
  *chosen conditionally on the measured head bit* `i` — it applies the classically-controlled
  single-wire phase cascade `qftTailBranch n i` (`Measurement.precompose`, on the tail factor via
  `Measurement.onRight`) and then recurses into `semiclassicalMeasuredQft n`;
* a **classical relabelling** of the recorded bits (`Measurement.reindexOutcome`) absorbing the
  Figure 5.1 output swaps — no swap *gate* survives.

The Figure 5.1 swaps only permute *which measured wire carries which output bit*, so for the outcome
**statistics** they are exactly this relabelling; the semiclassical circuit is therefore swap-free
and reproduces the measured QFT's probabilities identically
(`semiclassicalMeasuredQft_bornProb_eq`). This is the faithful whole-circuit content of Problem 5.2:
the quantum Fourier transform followed by a computational-basis measurement is equivalent — same
outcome distribution — to a circuit built entirely of one-qubit gates and measurement with classical
control. (The collapsed *states* agree up to the same final classical wire relabelling: the measured
QFT collapses to the recorded basis state `towerKet n r`
(`qftTowerEvolution_measure_postMeasurement_eq_towerKet`, above), and the semiclassical circuit to
its bit-reversal `towerKet n (fun i => r i.rev)` — the Figure 5.1 swaps become a classical
relabelling
(`semiclassicalMeasuredQft_postMeasurement_eq_towerKet`, the section that follows).)
-/

section SemiclassicalRealization

/-- **The outcome relabelling of the semiclassical realization.** It reads a full outcome
bit-string `r : Fin (n+2) → Fin 2` as a head bit together with a tail bit-string, through the
Figure 5.1 output permutation `σ = (finRotate (n+2)).symm`:
`r ↦ ⟨r (σ 0), fun i ↦ r (σ i.succ)⟩`. It is the head/tail split in which the swap layer becomes a
classical relabelling, so reindexing the semiclassical measurement's `Fin 2 × (Fin (n+1) → Fin 2)`
outcome (head bit, tail bit-string) by it lines the object up with the measured QFT wire for
wire. -/
def semiclassicalMeasuredQftOutcomeEquiv (n : ℕ) :
    (Fin (n + 2) → Fin 2) ≃ ((_ : Fin 2) × (Fin (n + 1) → Fin 2)) :=
  (Equiv.arrowCongr (finRotate (n + 2)) (Equiv.refl (Fin 2))).trans
    ((Fin.consEquiv (fun _ : Fin (n + 2) => Fin 2)).symm.trans
      (Equiv.sigmaEquivProd (Fin 2) (Fin (n + 1) → Fin 2)).symm)

/-- **The semiclassical realization of the measured quantum Fourier transform** (N&C Problem 5.2).
`semiclassicalMeasuredQft n : Measurement (Fin (n+1) → Fin 2) (qtower n qubit)` is the single
measurement object built *only* from one-qubit gates, computational-basis wire measurements, and
classical control — **no two-qubit gate** — whose outcome statistics equal those of the measured QFT
(`semiclassicalMeasuredQft_bornProb_eq`). It is defined by the outer tower recursion:

* at depth `0` the whole circuit is the single-wire Hadamard `qftTowerEvolution 0 = hadamardGate`
  followed by the measurement (`Measurement.precompose`);
* at depth `n+1` it applies the head-wire Hadamard `Evolution.qtowerSingleWire (n+1) 0 hadamardGate`
  (`Measurement.precompose`), measures the head wire (`controlMeasurement (qtower n qubit)`), and —
  **classically controlled** on the measured head bit `i` (`Measurement.adaptiveCascade`) — applies
  the single-wire phase cascade `qftTailBranch n i` to the remaining wires and recurses into
  `semiclassicalMeasuredQft n` (both on the tail factor, `Measurement.onRight`); the
  `Fin 2 × (Fin (n+1) → Fin 2)` (head bit, tail bit-string) outcome is relabelled to the full
  bit-string by `semiclassicalMeasuredQftOutcomeEquiv n`, absorbing the Figure 5.1 output swaps as a
  classical relabelling. -/
def semiclassicalMeasuredQft : (n : ℕ) → Measurement (Fin (n + 1) → Fin 2) (qtower n qubit)
  | 0 => (qtowerMeasurement 0).precompose hadamardGate
  | n + 1 =>
      (((controlMeasurement (qtower n qubit)).adaptiveCascade
          (fun i => ((semiclassicalMeasuredQft n).precompose (qftTailBranch n i)).onRight qubit)
        ).precompose (Evolution.qtowerSingleWire (n + 1) 0 hadamardGate)).reindexOutcome
          (semiclassicalMeasuredQftOutcomeEquiv n)

/-- **Problem 5.2 (the measured QFT's statistics are exactly those of the semiclassical circuit).**
The outcome statistics of the measured quantum Fourier transform — the QFT `qftTowerEvolution n`
followed by measuring every wire (`qtowerMeasurement n`) — equal, outcome for outcome and state
for state, those of the manifestly semiclassical circuit `semiclassicalMeasuredQft n`:

`p(r ∣ qftTowerEvolution n · ρ) = p(r ∣ semiclassicalMeasuredQft n · ρ)`.

Since `semiclassicalMeasuredQft n` is built only from one-qubit gates, computational-basis wire
measurements, and classical control — with no two-qubit gate — this is the faithful
whole-circuit content of Problem 5.2: the QFT plus a computational-basis measurement is
equivalent, as an outcome distribution, to a circuit of one-qubit gates and measurement with
classical control.
-/
theorem semiclassicalMeasuredQft_bornProb_eq :
    ∀ (n : ℕ) (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2),
      (qtowerMeasurement n).bornProb ((qftTowerEvolution n).evolve ρ) r
        = (semiclassicalMeasuredQft n).bornProb ρ r := sorry

end SemiclassicalRealization

/-! ### The semiclassical circuit collapses to the recorded basis state (outer tower induction)

The outcome **statistics** of the semiclassical circuit `semiclassicalMeasuredQft n` match the
measured QFT exactly (`semiclassicalMeasuredQft_bornProb_eq`, above). This section settles the
semiclassical circuit's side of the collapse-level content: what state it leaves the
register in for a given outcome `r`.

Like the measured QFT (`qftTowerEvolution_measure_postMeasurement_eq_towerKet`, above), the
semiclassical circuit collapses to a **recorded computational-basis state, independent of the
input**
`ρ` — but to `towerKet n (fun i => r i.rev)`, the **bit-reversal** of the measured QFT's collapse
`towerKet n r`:

  `postMeas(semiclassicalMeasuredQft n · ρ, r) = (towerKet n (fun i => r i.rev)).toState`.

The reversal `Fin.rev` is precisely the Figure 5.1 **swap network become a classical wire
relabelling**: `qftTowerEvolution n` is the *symmetric* DFT with the output swaps built in, so its
measured wires already carry the output bits in place (collapse `towerKet n r`); the semiclassical
circuit is swap-free (it absorbs the swaps as the outcome relabelling
`semiclassicalMeasuredQftOutcomeEquiv` for the statistics, no swap *gate*), so its measured wires
carry the same bits in the **reversed** order. Every leaf of the recursion is a computational-basis
wire measurement, so the collapse forgets the input entirely; the reversal accumulates one cyclic
`σ = (finRotate (n+2)).symm` per recursion level (head bit `r (σ 0) = r (Fin.last (n+1))` peeled to
the front at each step) into the full `Fin.rev`.

Together with the QFT-side collapse and the statistics equivalence, this is the collapse-level half
of Problem 5.2: the QFT-plus-measurement and the semiclassical circuit collapse to the **same**
computational-basis recording up to the bit-reversal wire relabelling the Figure 5.1 swap network
became — no two-qubit gate anywhere in the semiclassical circuit.
-/

section SemiclassicalCollapse

/-- **Problem 5.2 (the semiclassical circuit collapses to the recorded basis state).** The state
after the manifestly semiclassical circuit `semiclassicalMeasuredQft n` — one-qubit gates,
computational-basis wire measurements, and classical control, with **no two-qubit gate** —
collapses at outcome `r` to the computational-basis tower state `towerKet n (fun i => r i.rev)`,
**independent of the input** `ρ`:

`postMeas(semiclassicalMeasuredQft n · ρ, r) = (towerKet n (fun i => r i.rev)).toState`.

This is the **bit-reversal** `Fin.rev` of the measured QFT's collapse `towerKet n r`
(`qftTowerEvolution_measure_postMeasurement_eq_towerKet`) — exactly the Figure 5.1 swap network
become a classical wire relabelling: the swap-free semiclassical circuit records the output bits
in reversed wire order, differing from the symmetric-DFT measured QFT (whose swaps put the bits
in place) only by that relabelling. Every leaf of the circuit is a computational-basis wire
measurement, so the collapse forgets the input; the reversal is assembled from one cyclic `σ =
(finRotate (n+2)).symm` per level.
-/
theorem semiclassicalMeasuredQft_postMeasurement_eq_towerKet :
    ∀ (n : ℕ) (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2)
      (hpr : (semiclassicalMeasuredQft n).bornProb ρ r ≠ 0),
      (semiclassicalMeasuredQft n).postMeasurement ρ r hpr
        = (towerKet n (fun i => r i.rev)).toState := sorry

end SemiclassicalCollapse

/-! ### The semiclassical circuit contains no two-qubit gate

The equivalences above (`semiclassicalMeasuredQft_bornProb_eq`,
`semiclassicalMeasuredQft_postMeasurement_eq_towerKet`) match the measured QFT — statistics and
collapse — to the circuit `semiclassicalMeasuredQft n`. The **structural** half of Problem 5.2
remains: that the matching circuit uses *no two-qubit gate*.
`semiclassicalMeasuredQft n` is built only from the single-wire head Hadamard
`Evolution.qtowerSingleWire (n+1) 0 hadamardGate`, computational-basis wire measurements, classical
control, and — inside each classically-controlled branch — the phase cascade `qftTailBranch n i`.
The head Hadamard is a single-wire gate by construction; the theorem below exhibits the remaining
branch gate as a composition of single-wire gates. Together they show every gate of the
semiclassical circuit acts on a single wire. -/

/-- **Problem 5.2 (no two-qubit gate).** Each classically-controlled branch `qftTailBranch n i` of
the semiclassical circuit `semiclassicalMeasuredQft` is a **composition of single-wire gates**.

`qftTailBranch n i = (gs.map fun p => Evolution.qtowerSingleWire n p.1 p.2).prod`,

each factor `Evolution.qtowerSingleWire n t g` acting on the single tail wire `t` alone. Since the
only other gate of the circuit is the single-wire head Hadamard `Evolution.qtowerSingleWire
(n+1) 0 hadamardGate`, no gate of `semiclassicalMeasuredQft n` touches two wires — the "no two
qubit gates" conclusion of Problem 5.2, made an explicit proposition.
-/
theorem qftTailBranch_eq_qtowerSingleWire_prod (n : ℕ) (i : Fin 2) :
    ∃ gs : List (Fin (n + 1) × Evolution qubit),
      qftTailBranch n i = (gs.map fun p => Evolution.qtowerSingleWire n p.1 p.2).prod := sorry

end AxQM
