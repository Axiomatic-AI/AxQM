/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card

/-!
# Logical labeling for `n` spins: the largest effective pure state (Nielsen & Chuang, Ex. 7.44)

*Logical labeling* (§7.7.1, p. 334–335) prepares an **effective pure state** from a high-entropy
thermal NMR state in a single experiment. For `n` nearly identical spins in thermal equilibrium, the
high-temperature deviation density matrix is diagonal in the computational basis with *signal
population* on the basis state `|b⟩` proportional to the total magnetization
`n - 2·(Hamming weight of b)` (this is `Z₁ + ⋯ + Zₙ`; the isotropic background is unobservable
because NMR observables are traceless).

## Main results
* `magPop n A` — the signal population `n − 2·|A|` of the basis state `A` (magnetization, N&C's
  `6 − 4w` for `n = 3` up to the physically irrelevant overall scale `2`).
* `IsEffectivePureManifold n S` — `S` has the effective-pure population profile: a distinguished
  `g ∈ S` strictly above all others, and all the others mutually equal.
* `maxEffectivePureDim n := n.choose (n / 2) + 1` — the claimed answer.
* `IsEffectivePureManifold.card_le` — **optimality**: every effective-pure manifold has
  `S.card ≤ maxEffectivePureDim n`.
* `exists_isEffectivePureManifold` — **achievability**: for `n ≥ 1` an effective-pure manifold of
  cardinality exactly `maxEffectivePureDim n` exists.
-/

namespace AxQM.Concrete

/-- **Signal population of an `n`-spin computational basis state** (Nielsen & Chuang §7.7.1).
Modelling the basis state `|b⟩` by the set `A : Finset (Fin n)` of its spin-`|1⟩` positions (so the
Hamming weight of `b` is `A.card`), its high-temperature deviation population is the total
magnetization `n − 2·|A|` (the eigenvalue of `Z₁ + ⋯ + Zₙ`). For `n = 3` this is `(3, 1, 1, −1, …)`,
i.e. N&C's `(6, 2, 2, −2, …)` up to the physically irrelevant overall scale `2`. -/
def magPop (n : ℕ) (A : Finset (Fin n)) : ℤ := (n : ℤ) - 2 * (A.card : ℤ)

/-- **An effective-pure manifold.** A set `S` of `n`-spin computational basis states has the
population profile of an *effective pure state* `(1-ε)/d · I + ε|ψ⟩⟨ψ|`: there is a distinguished
ground state `g ∈ S` whose population strictly exceeds that of every other state of `S`, and all the
non-ground states of `S` share one common population. (Since logical labeling permutes the
populations, an arbitrary such subset is isolable, so these are exactly the effective pure states
constructible by logical labeling.) -/
def IsEffectivePureManifold (n : ℕ) (S : Finset (Finset (Fin n))) : Prop :=
  ∃ g ∈ S, (∀ A ∈ S, A ≠ g → magPop n A < magPop n g) ∧
    (∀ A ∈ S, ∀ B ∈ S, A ≠ g → B ≠ g → magPop n A = magPop n B)

/-- **The largest effective pure state constructible by logical labeling from `n` thermal spins**
(the answer to Exercise 7.44): dimension `n.choose (n/2) + 1`. -/
def maxEffectivePureDim (n : ℕ) : ℕ := n.choose (n / 2) + 1

/-- **Optimality (Exercise 7.44).** Every effective-pure manifold has at most
`maxEffectivePureDim n` states. -/
theorem IsEffectivePureManifold.card_le {n : ℕ} {S : Finset (Finset (Fin n))}
    (h : IsEffectivePureManifold n S) : S.card ≤ maxEffectivePureDim n := sorry

/-- **Achievability (Exercise 7.44).** For `n ≥ 1` spins there is an effective-pure manifold of
cardinality exactly `maxEffectivePureDim n`. -/
theorem exists_isEffectivePureManifold {n : ℕ} (hn : 1 ≤ n) :
    ∃ S : Finset (Finset (Fin n)),
      IsEffectivePureManifold n S ∧ S.card = maxEffectivePureDim n := sorry

end AxQM.Concrete
