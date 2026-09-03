/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.Problem12_1

/-!
# N&C Theorem 12.1 — the Holevo bound

*(N&C p. 531.)*

Holevo bound: H(X:Y) <= S(rho) - sum p_x S(rho_x) for any POVM.

* `holevo_bound` — `H(X : Y) ≤ S(ρ) − ∑ₓ pₓ S(ρₓ)`, for any measurement Bob may perform.
-/

noncomputable section

namespace AxQM

/-- **N&C Theorem 12.1 (the Holevo bound)** (eq. (12.6)). Alice prepares `ρₓ` with probability `pₓ`
(random variable `X` over the finite index `κ`); Bob performs the POVM measurement `m` and
obtains outcome `Y` (over `Fin r`). Then the classical mutual information of the joint
distribution `p(x, y) = pₓ · m.bornProb (ρₓ) y` of `X` and `Y` is bounded by the Holevo χ
quantity of Alice's ensemble:

`H(X : Y) ≤ S(ρ) − ∑ₓ pₓ S(ρₓ)`,    where `ρ = ∑ₓ pₓ ρₓ`,

the right-hand side being the entropy of the average state minus the average of the component
entropies. Holds for any measurement Bob may perform, with no restriction on the ensemble or the
dimension.
-/
theorem holevo_bound {Q : QSystem} {r : ℕ} [NeZero r] {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (ρ : κ → State Q)
    (m : Measurement (Fin r) Q) :
    Real.mutualInfo (fun xy : κ × Fin r => p xy.1 * m.bornProb (ρ xy.1) xy.2)
      ≤ (State.mix p hp hsum ρ).vonNeumannEntropy - ∑ x, p x * (ρ x).vonNeumannEntropy := sorry

end AxQM
