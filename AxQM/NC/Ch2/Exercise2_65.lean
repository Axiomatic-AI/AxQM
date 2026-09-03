/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.RelativePhase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Nielsen & Chuang, Exercise 2.65 (relative phase is basis-dependent)

*(N&C p. 93.)*

Express (|0>±|1>)/sqrt2 in a basis where not the same up to a relative phase.

* `plusMinusFrame` — the frame `⟨|+⟩, |-⟩⟩`, i.e. N&C's answer basis.
* `not_qubitPlus_qubitMinus_relativePhaseEquiv_plusMinusFrame` — in the `{|+⟩, |-⟩}` basis they are
  not relative-phase equivalent (the required amplitude-magnitude equality `1 = 0` fails).
-/

open scoped InnerProductSpace

namespace AxQM

/-- The frame `⟨|+⟩, |-⟩⟩` — the orthonormal basis `{|+⟩, |-⟩}` of the qubit, as a family of pure
states. This is the basis N&C asks for: the one in which `|+⟩` and `|-⟩` are *not* relative-phase
equivalent. -/
noncomputable def plusMinusFrame : Fin 2 → PureState qubit := ![qubitPlus, qubitMinus]

/-- **Nielsen & Chuang, Exercise 2.65 (the answer).** In the basis `{|+⟩, |-⟩}`, the states `|+⟩`
and `|-⟩` are **not** the same up to a relative phase shift. Physically: in its own basis `|+⟩`
has amplitudes `(1, 0)` and `|-⟩` has `(0, 1)`, whose magnitudes differ, so no per-amplitude
phase can relate them. -/
theorem not_qubitPlus_qubitMinus_relativePhaseEquiv_plusMinusFrame :
    ¬ PureState.RelativePhaseEquiv plusMinusFrame qubitPlus qubitMinus := sorry

end AxQM
