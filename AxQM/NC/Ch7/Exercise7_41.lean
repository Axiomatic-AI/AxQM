/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.NMRControlledZ

/-!
# Nielsen & Chuang, Exercise 7.41 (NMR controlled-`Z`)

*(N&C p. 332.)*

NMR controlled-NOT: give explicit single-qubit rotation sequence realizing CNOT under Hamiltonian
(7.147).

* `nmrControlledZ_globalPhase_eq_controlledZGate` — the exact gate identity: for `c·t = π/4`,
  `globalPhaseGate(-π/4) ∘ nmrControlledZSequence c t = controlledZGate`.
* `nmrControlledZSequence_evolve_eq_controlledZGate` — the physics reading (the channel): for `c·t =
  π/4`, the pulse sequence `nmrControlledZSequence c t` induces the *same state channel* `ρ ↦ U ρ
  U†` as the controlled-`Z` gate, on every state.
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 7.41 — the exact gate identity (eq. 7.152).** For one period of
`Z₁Z₂`-coupled evolution with `c·t = π/4`, the pulse sequence `nmrControlledZSequence c t`
(coupled evolution + a `R_z(-π/2)` on each spin) equals the controlled-`Z` gate up to the global
phase `√(-i) = e^{-iπ/4}`:

`globalPhaseGate(-π/4) ∘ nmrControlledZSequence c t = controlledZGate`.

This is N&C's construction `√i · e^{iZ₁Z₂π/4} · e^{-iZ₁π/4} · e^{-iZ₂π/4} = diag(1,1,1,-1)` as
an `Evolution` equality (in the positive-coupling-time convention, so `√i` becomes `√(-i)`).
-/
theorem nmrControlledZ_globalPhase_eq_controlledZGate (c t : ℝ) (h : c * t = Real.pi / 4) :
    (globalPhaseGate (-(Real.pi / 4))).comp (nmrControlledZSequence c t) = controlledZGate := sorry

/-- **Nielsen & Chuang, Exercise 7.41 — the physics reading (channel equality).** For one period of
`Z₁Z₂`-coupled evolution with `c·t = π/4`, the NMR pulse sequence `nmrControlledZSequence c t` —
the coupled evolution `exp(-i c Z₁Z₂ t)` followed by a `90°` `z`-rotation `R_z(-π/2)` on each
spin — induces the *same state channel* `ρ ↦ U ρ U†` as the controlled-`Z` gate, on every state
`ρ`. The `√(-i)` global phase of the gate identity is physically unobservable, so these two
single-qubit rotations plus one coupling period realise a controlled-`Z` between the two coupled
spins. -/
theorem nmrControlledZSequence_evolve_eq_controlledZGate (c t : ℝ) (h : c * t = Real.pi / 4)
    (ρ : State (qubit ⊗ qubit)) :
    (nmrControlledZSequence c t).evolve ρ = controlledZGate.evolve ρ := sorry

end AxQM
