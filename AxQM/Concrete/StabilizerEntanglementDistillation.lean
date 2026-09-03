/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.ToMathlib.LinearAlgebra.Matrix.MaxEntVec
import AxQM.Concrete.StabilizerCodeDistance

/-!
# Concrete: entanglement distillation of EPR pairs by a stabilizer code (N&C Ex 12.34)

Nielsen & Chuang, **Exercise 12.34** (*Entanglement distillation by error-correction*, p. 597),
parts (a) and (b).
-/

open Matrix
open scoped Kronecker Matrix

namespace AxQM.Concrete

variable {n : ℕ} {S : Subgroup (PauliGroup n)} [Fintype ↥S]

/-- The **distilled entangled state** of `n` EPR pairs by the stabilizer code with stabilizer `S`:
the maximally entangled vector `|m⟩ = maxEntVec (Fin n → Fin 2) ℂ` with **one** half projected onto
the code space `V_S = range (codeProjector S)`, i.e. `(P_S ⊗ I)|m⟩`. This is the (unnormalised)
maximally entangled state on `V_S`; for an `[n, m]` stabilizer code `V_S` is `2ᵐ`-dimensional, so
this is the encoded `|β₀₀⟩^⊗m` of Nielsen & Chuang, Exercise 12.34(a). -/
noncomputable def stabilizerDistilledVec (S : Subgroup (PauliGroup n)) [Fintype ↥S] :
    (Fin n → Fin 2) × (Fin n → Fin 2) → ℂ :=
  (codeProjector S ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)).mulVec
    (maxEntVec (Fin n → Fin 2) ℂ)

/-- **Matched syndromes (identical measurements on both halves = one code-space projection).**
The physical operation of Exercise 12.34(a) — identical stabilizer-generator measurements on the
two `n`-qubit halves plus Pauli correction — projects **both** halves of the maximally entangled
state onto the code space. On the second (Bob) leg identical measurements act as the entrywise
conjugate `(codeProjector S).map star = (codeProjector S)̄`. This two-sided projection equals the
single-sided `stabilizerDistilledVec S`. -/
theorem stabilizerDistilledVec_bothHalves :
    (codeProjector S ⊗ₖ (codeProjector S).map star).mulVec (maxEntVec (Fin n → Fin 2) ℂ)
      = stabilizerDistilledVec S := sorry

/-- **The distilled state is the encoded `|β₀₀⟩^⊗m`.** For an `[n, m]` stabilizer code — `m ≤ n`
logical qubits, so the stabilizer has `n - m` generators and order `|S| = 2ⁿ⁻ᵐ` — the distilled
state has squared norm `2ᵐ`. Since the (unnormalised) maximally entangled state on a
`d`-dimensional space has squared norm `d`, this exhibits `stabilizerDistilledVec S` as the
maximally entangled state on the `2ᵐ`-dimensional code space `V_S`: `m` encoded Bell pairs, i.e. the
encoded `|β₀₀⟩^⊗m` of Nielsen & Chuang, Exercise 12.34(a). -/
theorem stabilizerDistilledVec_normSq_eq_two_pow {m : ℕ} (hneg : PauliGroup.negOne n ∉ S)
    (hmn : m ≤ n) (hcard : Fintype.card ↥S = 2 ^ (n - m)) :
    star (stabilizerDistilledVec S) ⬝ᵥ stabilizerDistilledVec S = 2 ^ m := sorry

/-- **Part (b) in the textbook's parameters.** For an `[n, m]` stabilizer code correcting up to
`t = δn` errors — distance at least `2t + 1` (`hdist`) — if a Pauli error `E` of weight `≤ t` is
suffered by one `n`-qubit half and the syndrome-based correction `C` also has weight `≤ t` and the
same syndrome (`C * E ∈ N(S)`), then the distilled state is recovered up to a unit-modulus phase —
the `m` encoded Bell pairs survive `δn` errors on one `n`-qubit half. -/
theorem stabilizerDistilledVec_error_corrected_of_weight_le {E C : PauliGroup n} {t : ℕ}
    (hE : E.weight ≤ t) (hC : C.weight ≤ t)
    (hdist : (2 * t + 1 : ℕ∞) ≤ stabilizerCodeDistance S)
    (hsynd : C * E ∈ Subgroup.normalizer S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ((codeProjector S * C.toMat * E.toMat) ⊗ₖ (codeProjector S).map star).mulVec
          (maxEntVec (Fin n → Fin 2) ℂ)
        = c • stabilizerDistilledVec S := sorry

end AxQM.Concrete
