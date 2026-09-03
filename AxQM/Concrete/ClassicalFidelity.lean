/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Tactic

/-!
# Classical fidelity between probability distributions (Nielsen & Chuang §9.1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §9.1 (p. 400)
introduce the **fidelity** of two probability distributions `{pₓ}` and `{qₓ}`
over a common finite index set, N&C equation `(9.2)`:
```
F(pₓ, qₓ) ≡ ∑ₓ √(pₓ qₓ).
```
Geometrically this is the inner product `⟨(√pₓ), (√qₓ)⟩` of the two vectors of
coordinate-wise square roots, which lie on the unit sphere (N&C Figure 9.1); it
is also known as the Bhattacharyya coefficient. Unlike the trace distance it is
*not* a metric — N&C note that for identical distributions `F(pₓ, pₓ) = ∑ₓ pₓ = 1`
(a maximum, not a zero) — but a metric can be derived from it.

## Main definitions

* `classicalFidelity` — the fidelity `∑ₓ √(pₓ qₓ)` of `(9.2)`.

## Main statements

* `classicalFidelity_deterministic_uniform` — **Exercise 9.3, part 1**: the
  fidelity between the deterministic distribution `(1, 0)` and the uniform
  distribution `(1/2, 1/2)` is `√2 / 2` (i.e. `1/√2`).
* `classicalFidelity_ternary_example` — **Exercise 9.3, part 2**: the fidelity
  between `(1/2, 1/3, 1/6)` and `(3/4, 1/8, 1/8)` is `(4√6 + √3) / 12`.
-/

namespace AxQM.Concrete

open scoped BigOperators

/-- The **classical fidelity** between two probability distributions
`p, q : ι → ℝ` over a finite index set, Nielsen & Chuang `(9.2)`:
`F(pₓ, qₓ) ≡ ∑ₓ √(pₓ qₓ)`. Also known as the Bhattacharyya coefficient; it is the
inner product of the vectors of coordinate-wise square roots (N&C Figure 9.1). -/
noncomputable def classicalFidelity {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ x, Real.sqrt (p x * q x)

/-- **Nielsen & Chuang, Exercise 9.3 (part 1).** The fidelity between the
deterministic distribution `(1, 0)` and the uniform distribution `(1/2, 1/2)` is
`√2 / 2` (equivalently `1/√2`). -/
theorem classicalFidelity_deterministic_uniform :
    classicalFidelity ![1, 0] ![1 / 2, 1 / 2] = Real.sqrt 2 / 2 := sorry

/-- **Nielsen & Chuang, Exercise 9.3 (part 2).** The fidelity between
`(1/2, 1/3, 1/6)` and `(3/4, 1/8, 1/8)` is `(4√6 + √3) / 12`. -/
theorem classicalFidelity_ternary_example :
    classicalFidelity ![1 / 2, 1 / 3, 1 / 6] ![3 / 4, 1 / 8, 1 / 8]
      = (4 * Real.sqrt 6 + Real.sqrt 3) / 12 := sorry

end AxQM.Concrete
