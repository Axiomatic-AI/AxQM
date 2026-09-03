/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.LinearOpticalElement
import AxQM.Concrete.QFTTwoLevel
import AxQM.Concrete.TwoLevelEmbedding
import AxQM.Concrete.ControlledSingleQubit
import Mathlib.LinearAlgebra.Matrix.Swap
import AxQM.Concrete.TwoLevelLowerBound
import AxQM.Basic.API.QuditGate
import AxQM.Basic.API.DeutschAlgorithm
import AxQM.Basic.API.Reflection
import AxQM.Basic.API.UniformSuperposition
import AxQM.Basic.API.QuditTensorFactor

/-!
# N&C Problem 7.2 (Computing with linear optics) — universality and the exponential lower bound

*(N&C p. 346.)*

Computing with linear optics: for unary photon encoding, show any unitary is built from
beamsplitters/phase shifters; DJ + search circuits; and arbitrary U needs exponentially many
components.

* `phaseShifterGate`
* `beamSplitterGate`
* `IsLinearOpticalGate`
* `linearOptics_universal` — Part 1: for `d ≥ 2`, every unitary `Evolution (qudit d)` is the ordered
  composition (monoid product of a finite list) of linear-optical gates.
* `unaryEncoding` — the unary encoding of a two-qubit register: the system isomorphism `qubit ⊗
  qubit ≃ₛ qudit 4` identifying a computational basis state `|k⟩` (`k = 0,1,2,3`) with a single
  photon in mode `k` of four optical modes.
* `deutschCircuitUnary`
* `linearOptics_deutschJozsa` — Part 2: for every oracle `Uf`, the unary-encoded Deutsch–Jozsa
  circuit `deutschCircuitUnary Uf` is a beamsplitter/phase-shifter product — no nonlinear media.
* `searchOracleUnary` — the search oracle `O_x = I − 2|x⟩⟨x|` in the unary encoding.
* `searchDiffusionUnary` — the inversion-about-the-mean diffusion in the unary encoding.
* `twoQubitSearchStep` — the Grover iterate `G = D · O_x` in the unary encoding.
* `linearOptics_twoQubitSearch` — Part 3: for every marked mode `x`, the Grover iterate
  `twoQubitSearchStep x` is a beamsplitter/phase-shifter product — again no nonlinear media.
* `linearOptics_exponential_lower_bound` — Part 4 (the `n`-qubit reading): on the physical `d =
  2ⁿ`-mode system, some unitary needs at least `2ⁿ − 1` gates — exponentially many in `n`.
-/

open AxQM.Concrete Matrix

noncomputable section

namespace AxQM

variable {d : ℕ}

/-! ### The two linear-optical gates -/

/-- **Phase shifter on optical mode `p`** as an `Evolution (qudit d)`: the gate whose operator is
the phase-shifter matrix `Concrete.phaseMode p φ = diag(…, e^{iφ}, …)`. It multiplies the amplitude
of mode `p` by the phase `e^{iφ}` and fixes every other mode. -/
def phaseShifterGate (p : Fin d) (φ : ℝ) : Evolution (qudit d) :=
  quditGate (phaseMode_mem_unitaryGroup p φ)

/-- **Beamsplitter mixing optical modes `p ≠ q`** as an `Evolution (qudit d)`: the gate whose
operator is the beamsplitter matrix `Concrete.beamSplitter p q θ`, applying the real `2 × 2`
rotation `R_y(θ)` to the amplitudes of modes `p, q` and fixing the rest. -/
def beamSplitterGate (p q : Fin d) (θ : ℝ) (h : p ≠ q) : Evolution (qudit d) :=
  quditGate (beamSplitter_mem_unitaryGroup h θ)

/-- **A linear-optical gate** is a beamsplitter (on a genuine pair `p ≠ q`) or a phase shifter — the
two passive optical elements Problem 7.2 allows. -/
def IsLinearOpticalGate (V : Evolution (qudit d)) : Prop :=
  (∃ (p q : Fin d) (θ : ℝ) (h : p ≠ q), V = beamSplitterGate p q θ h) ∨
    (∃ (p : Fin d) (φ : ℝ), V = phaseShifterGate p φ)

/-! ### Universality (Problem 7.2, Part 1) -/

/-- **Universality of linear optics (Nielsen & Chuang, Problem 7.2, Part 1).** For `d ≥ 2`, every
unitary `Evolution (qudit d)` is a finite ordered composition of linear-optical gates: there is
a list `L` of `Evolution (qudit d)`, each of which `IsLinearOpticalGate` (a beamsplitter or a
phase shifter), whose monoid product `L.prod` equals `E`. Physically, on the unary-encoded
single-photon system (`d = 2ⁿ` modes) an arbitrary `n`-qubit unitary is realized entirely by
beamsplitters and phase shifters, with no nonlinear media.
-/
theorem linearOptics_universal (hd : 2 ≤ d) (E : Evolution (qudit d)) :
    ∃ L : List (Evolution (qudit d)), (∀ V ∈ L, IsLinearOpticalGate V) ∧ L.prod = E := sorry

/-! ### Deutsch–Jozsa in the unary encoding (Problem 7.2, Part 2) -/

/-- **The unary encoding of a two-qubit register.** The system isomorphism
`qubit ⊗ qubit ≃ₛ qudit 4` identifying the two-qubit computational basis state `|k⟩`
(`k ∈ {0,1,2,3}`) with a single photon in mode `k` of four optical modes — Problem 7.2's unary
representation for `n = 2` (`|01⟩ = 0`, `|10⟩ = 1`, …). The computational-basis identification is
`|x⟩ ⊗ |y⟩ ↦ |2x + y⟩`. -/
def unaryEncoding : (qubit ⊗ qubit) ≃ₛ qudit 4 := (quditProdIso 2 2).symm

/-- **Deutsch's circuit in the unary encoding.** Deutsch's circuit `(H ⊗ I) · U_f · (H ⊗ H)`
(`deutschCircuit Uf`) transported along the unary encoding `unaryEncoding` into the four-mode
picture, as an `Evolution (qudit 4)`. -/
def deutschCircuitUnary (Uf : Evolution (qubit ⊗ qubit)) : Evolution (qudit 4) :=
  Evolution.congr unaryEncoding (deutschCircuit Uf)

/-- **Optical realization of the Deutsch–Jozsa circuit (Nielsen & Chuang, Problem 7.2, Part 2).**
For *every* oracle `Uf`, the unary-encoded Deutsch–Jozsa circuit `deutschCircuitUnary Uf` is a
finite beamsplitter/phase-shifter product: a list `L` of linear-optical gates (each
`IsLinearOpticalGate`) whose monoid product is `deutschCircuitUnary Uf`. So the one-qubit
Deutsch–Jozsa algorithm — including its oracle, whatever it is — is realized in the unary encoding
by beamsplitters and phase shifters alone, **with no nonlinear media**. -/
theorem linearOptics_deutschJozsa (Uf : Evolution (qubit ⊗ qubit)) :
    ∃ L : List (Evolution (qudit 4)), (∀ V ∈ L, IsLinearOpticalGate V) ∧
      L.prod = deutschCircuitUnary Uf := sorry

/-! ### Two-qubit quantum search in the unary encoding (Problem 7.2, Part 3) -/

/-- **The two-qubit search oracle in the unary encoding.** For a marked mode `x : Fin 4`, the oracle
`O_x = I − 2|x⟩⟨x|` (Nielsen & Chuang §6.1.1) that flips the phase of the marked computational basis
state `|x⟩` and fixes the others, as an `Evolution (qudit 4)`. -/
def searchOracleUnary (x : Fin 4) : Evolution (qudit 4) := reflectionEvolution (quditBasis x)

/-- **The inversion-about-the-mean diffusion in the unary encoding.** The reflection about the
uniform superposition `|ψ⟩ = ½ ∑ₖ |k⟩` of the four modes (Nielsen & Chuang eq. 6.6), as an
`Evolution (qudit 4)`. `reflectionEvolution` gives `I − 2|ψ⟩⟨ψ|`, which is N&C's `2|ψ⟩⟨ψ| − I` up to
the physically irrelevant global phase `−1` — the same reflection of the two-dimensional Grover
plane spanned by `|ψ⟩` and the marked state. -/
def searchDiffusionUnary : Evolution (qudit 4) := reflectionEvolution (uniformSuperposition 4)

/-- **One Grover iteration of the two-qubit search algorithm, in the unary encoding.** The Grover
iterate `G = D · O_x` (Nielsen & Chuang §6.1.2): the search oracle `searchOracleUnary x` followed by
the inversion-about-the-mean diffusion `searchDiffusionUnary`, as an `Evolution (qudit 4)`. For a
two-qubit (`N = 4`) search a single iteration rotates the uniform superposition onto the marked
mode; this is the active step of the two-qubit search algorithm of Problem 7.2 Part 3. -/
def twoQubitSearchStep (x : Fin 4) : Evolution (qudit 4) :=
  searchDiffusionUnary.comp (searchOracleUnary x)

/-- **Optical realization of the two-qubit quantum-search circuit (Nielsen & Chuang, Problem 7.2,
Part 3).** For *every* marked mode `x`, the Grover iterate `twoQubitSearchStep x` is a finite
beamsplitter/phase-shifter product: a list `L` of linear-optical gates (each `IsLinearOpticalGate`)
whose monoid product is `twoQubitSearchStep x`. So the two-qubit quantum-search algorithm — oracle
*and* diffusion — is realized in the unary encoding by beamsplitters and phase shifters alone,
**with no nonlinear media**. -/
theorem linearOptics_twoQubitSearch (x : Fin 4) :
    ∃ L : List (Evolution (qudit 4)), (∀ V ∈ L, IsLinearOpticalGate V) ∧
      L.prod = twoQubitSearchStep x := sorry

/-! ### Exponential lower bound (Problem 7.2, Part 4) -/

/-- **Exponential component lower bound in the number of qubits (Nielsen & Chuang, Problem 7.2, Part
4).** In the unary encoding of Problem 7.2, an `n`-qubit register is `d = 2ⁿ` optical modes
(`qudit (2ⁿ)`). So although Part 1 shows any unitary *can* be built from just these two passive
elements, in general doing so requires an exponential number of components, as Problem 7.2 Part 4
asks. -/
theorem linearOptics_exponential_lower_bound (n : ℕ) :
    ∃ E : Evolution (qudit (2 ^ n)), ∀ L : List (Evolution (qudit (2 ^ n))),
      (∀ V ∈ L, IsLinearOpticalGate V) → L.prod = E → 2 ^ n - 1 ≤ L.length := sorry

end AxQM
