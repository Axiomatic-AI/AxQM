/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Interchange
import AxQM.Basic.Composite
import AxQM.Basic.PartialTrace
import AxQM.Basic.SystemIso
import AxQM.Basic.Evolution
import AxQM.ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# AxQM — the environment-model channel with different input/output spaces (N&C Ex 8.3)

The physics realizing **Nielsen–Chuang Exercise 8.3** (the generalization of the
operator-sum derivation of §8.2.3 to *different input and output spaces*).

## Contents

* `AxQM.envModelChannel` — the channel `E(ρ)`, built from the primitives as
  `((U.evolve (ρ ⊗ |0⟩⟨0|)).congr Φ).reducedLeft`, where the transport `Φ = interchangeBCAD` first
  regroups `(A ⊗ B) ⊗ (C ⊗ D)` into `(B ⊗ C) ⊗ (A ⊗ D)` so that `State.reducedLeft` (which traces
  out the *right* factor) discards exactly `A ⊗ D` and keeps `B ⊗ C`.
* `AxQM.envModelChannel_hasOperatorSum` — **the exercise:** the channel `E` has an
  operator-sum representation with operation elements `Eₖ : (A ⊗ B).space →ₗ (B ⊗ C).space`
  satisfying `E(ρ) = ∑ₖ Eₖ ρ Eₖ†` (eq. 8.15) *and* the completeness relation `∑ₖ Eₖ† Eₖ = I` (making
  `E` trace preserving). The two are witnessed by the *same* family, as N&C requires.
-/

open scoped InnerProductSpace

open LinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {A B C D : QSystem}

/-- **The environment-model channel (Nielsen & Chuang Exercise 8.3).**  A principal system `A ⊗ B`
in state `ρ` and an environment `C ⊗ D` in a standard pure state `ω = |0⟩` interact by the joint
unitary `U`; systems `A` and `D` are then discarded, leaving `B ⊗ C`. -/
def envModelChannel (ω : PureState (C ⊗ D)) (U : Evolution ((A ⊗ B) ⊗ (C ⊗ D)))
    (ρ : State (A ⊗ B)) : State (B ⊗ C) :=
  ((U.evolve (ρ.tmul ω.toState)).congr (QSystem.interchangeBCAD A B C D)).reducedLeft

set_option maxHeartbeats 400000 in
-- The definitional bridge between the composite-system space `(S ⊗ T).space` (bundled `QSystem`
-- instances) and the raw `TensorProduct` the fork operator-sum package is stated over is costly to
-- reconcile (the `InnerProductSpace` instances agree definitionally but not syntactically).
/-- **Nielsen & Chuang, Exercise 8.3.**  Discarding subsystems `A` and `D` after a joint unitary
interaction of a principal system `A ⊗ B` (in state `ρ`) with an environment `C ⊗ D` (prepared in a
standard pure state `ω`) yields a channel `E = envModelChannel ω U : State (A ⊗ B) → State (B ⊗ C)`
in operator-sum form: there is a family of operation elements `Eₖ : (A ⊗ B).space →ₗ (B ⊗ C).space`
with

* `E(ρ) = ∑ₖ Eₖ ρ Eₖ†`   (eq. 8.15), and
* `∑ₖ Eₖ† Eₖ = I`         (eq. 8.14 — completeness / trace preservation),

both witnessed by the *same* family. -/
theorem envModelChannel_hasOperatorSum (ω : PureState (C ⊗ D))
    (U : Evolution ((A ⊗ B) ⊗ (C ⊗ D))) :
    ∃ (ι : Type) (_ : Fintype ι) (E : ι → ((A ⊗ B).space →ₗ[ℂ] (B ⊗ C).space)),
      (∀ ρ : State (A ⊗ B),
          (↑(envModelChannel ω U ρ).op : (B ⊗ C).space →ₗ[ℂ] (B ⊗ C).space)
            = ∑ k, E k ∘ₗ (↑ρ.op) ∘ₗ LinearMap.adjoint (E k)) ∧
        ∑ k, LinearMap.adjoint (E k) ∘ₗ E k = LinearMap.id := sorry

end AxQM
