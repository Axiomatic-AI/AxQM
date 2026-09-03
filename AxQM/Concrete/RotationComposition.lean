/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochRotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Concrete: composition of two Bloch-sphere rotations (Nielsen & Chuang, Exercise 4.15)

Nielsen & Chuang, Exercise 4.15 ("Composition of single qubit operations") asks: if a rotation
through `β₁` about `n̂₁` is followed by one through `β₂` about `n̂₂`, the overall operation is
again a rotation, through some angle `β₁₂` about some axis `n̂₁₂`; find `β₁₂, n̂₁₂` (eq. 4.19–4.20)
and specialise to `β₁ = β₂`, `n̂₁ = ẑ` (eq. 4.21–4.22).

## Main declarations
* `rotComposeCos` / `rotComposeVec` — the composed half-angle cosine `c₁₂` (eq. 4.19) and the
  composed axis-vector `s₁₂ n̂₁₂` (eq. 4.20, corrected sign) for the order "`n̂₁` then `n̂₂`".
* `rotAxis_mul_rotAxis` — **part (1)**: `R_n̂₂(β₂) R_n̂₁(β₁) = c₁₂ I − i (s₁₂ n̂₁₂)·σ`, the
  composition law, for arbitrary unit axes and angles.
* `rotComposeCos_self_axisZ` / `rotComposeVec_self_axisZ` — **part (2)**: the `β₁ = β₂`, `n̂₁ = ẑ`
  simplifications (eq. 4.21 and eq. 4.22, corrected sign).
* `rotAxis_mul_rotAxis_stated_order_printed_false` — a formal refutation: at `n̂₁ = ẑ, n̂₂ = x̂,
  β₁ = β₂ = π` the composite `R_x(π) R_z(π)` differs from the operator built from N&C's printed
  axis-vector, so the printed eq. (4.20) is false for the stated order.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The **composed half-angle cosine** `c₁₂ = c₁c₂ − s₁s₂ (n̂₁·n̂₂)` of a rotation by `β₁` about
`n₁` followed by a rotation by `β₂` about `n₂` (Nielsen & Chuang, eq. 4.19), with `cᵢ = cos(βᵢ/2)`,
`sᵢ = sin(βᵢ/2)`. Symmetric in the two rotations. -/
noncomputable def rotComposeCos (β₁ : ℝ) (n₁ : Fin 3 → ℝ) (β₂ : ℝ) (n₂ : Fin 3 → ℝ) : ℝ :=
  Real.cos (β₁ / 2) * Real.cos (β₂ / 2)
    - Real.sin (β₁ / 2) * Real.sin (β₂ / 2) * (n₁ ⬝ᵥ n₂)

/-- The **composed axis-vector** `s₁₂ n̂₁₂ = s₁c₂ n̂₁ + c₁s₂ n̂₂ + s₁s₂ (n̂₂×n̂₁)` of a rotation by
`β₁` about `n₁` followed by a rotation by `β₂` about `n₂` (Nielsen & Chuang, eq. 4.20), with
`cᵢ = cos(βᵢ/2)`, `sᵢ = sin(βᵢ/2)`. The cross-product sign is `+ s₁s₂ n̂₂×n̂₁`, correcting the
printed `− s₁s₂ n̂₂×n̂₁`. -/
noncomputable def rotComposeVec (β₁ : ℝ) (n₁ : Fin 3 → ℝ) (β₂ : ℝ) (n₂ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (Real.sin (β₁ / 2) * Real.cos (β₂ / 2)) • n₁ + (Real.cos (β₁ / 2) * Real.sin (β₂ / 2)) • n₂
    + (Real.sin (β₁ / 2) * Real.sin (β₂ / 2)) • crossProduct n₂ n₁

/-- **Composition of two Bloch-sphere rotations — Nielsen & Chuang, Exercise 4.15 (1).** A rotation
by `β₁` about the unit axis `n₁` followed by a rotation by `β₂` about the unit axis `n₂` — the
operator product `R_n̂₂(β₂) R_n̂₁(β₁)` — is again a rotation operator `R_n̂₁₂(β₁₂) = c₁₂ I − i
(s₁₂ n̂₁₂)·σ`, whose composed cosine `c₁₂` and axis-vector `s₁₂ n̂₁₂` are `rotComposeCos` (eq.
4.19) and `rotComposeVec` (eq. 4.20). Both axes are fully general unit vectors and both angles
are arbitrary. -/
theorem rotAxis_mul_rotAxis {n₁ n₂ : Fin 3 → ℝ}
    (h₁ : n₁ 0 ^ 2 + n₁ 1 ^ 2 + n₁ 2 ^ 2 = 1)
    (h₂ : n₂ 0 ^ 2 + n₂ 1 ^ 2 + n₂ 2 ^ 2 = 1) (β₁ β₂ : ℝ) :
    rotAxis n₂ β₂ * rotAxis n₁ β₁
      = (rotComposeCos β₁ n₁ β₂ n₂ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        - Complex.I • pauliDot (rotComposeVec β₁ n₁ β₂ n₂) := sorry

/-- **Special case of the composed cosine — Nielsen & Chuang, Exercise 4.15 (2), eq. 4.21.** When
the two rotations share the angle (`β₁ = β₂ = β`) and the first axis is `ẑ`, the composed half-angle
cosine `c₁₂` becomes `c² − s² (ẑ·n̂₂)` with `c = cos(β/2)`, `s = sin(β/2)`. -/
theorem rotComposeCos_self_axisZ (β : ℝ) (n₂ : Fin 3 → ℝ) :
    rotComposeCos β ![0, 0, 1] β n₂
      = Real.cos (β / 2) ^ 2 - Real.sin (β / 2) ^ 2 * ((![0, 0, 1] : Fin 3 → ℝ) ⬝ᵥ n₂) := sorry

/-- **Special case of the composed axis-vector — Nielsen & Chuang, Exercise 4.15 (2), eq. 4.22.**
When the two rotations share the angle (`β₁ = β₂ = β`) and the first axis is `ẑ`, the composed
axis-vector `s₁₂ n̂₁₂` becomes `sc (ẑ + n̂₂) + s² (n̂₂ × ẑ)` with `c = cos(β/2)`, `s = sin(β/2)`.
The cross-product sign is `+ s² n̂₂×ẑ`, correcting the printed `− s² n̂₂×ẑ` (the same
order-transposition erratum as in eq. 4.20). -/
theorem rotComposeVec_self_axisZ (β : ℝ) (n₂ : Fin 3 → ℝ) :
    rotComposeVec β ![0, 0, 1] β n₂
      = (Real.sin (β / 2) * Real.cos (β / 2)) • ((![0, 0, 1] : Fin 3 → ℝ) + n₂)
        + Real.sin (β / 2) ^ 2 • crossProduct n₂ ![0, 0, 1] := sorry

/-- **The exercise as printed is false for the stated order: a formal refutation of eq. (4.20).**
For the unit axes `n̂₁ = ẑ`, `n̂₂ = x̂` and `β₁ = β₂ = π`, the composite `R_x(π) R_z(π)` (the
"`ẑ` then `x̂`" order of the text) does *not* equal the rotation operator built from N&C's
printed axis-vector `s₁c₂ n̂₁ + c₁s₂ n̂₂ − s₁s₂ n̂₂×n̂₁` (cross sign opposite to
`rotComposeVec`). -/
theorem rotAxis_mul_rotAxis_stated_order_printed_false :
    rotAxis ![1, 0, 0] Real.pi * rotAxis ![0, 0, 1] Real.pi
      ≠ (rotComposeCos Real.pi ![0, 0, 1] Real.pi ![1, 0, 0] : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        - Complex.I • pauliDot
            ((Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2)) • (![0, 0, 1] : Fin 3 → ℝ)
              + (Real.cos (Real.pi / 2) * Real.sin (Real.pi / 2)) • (![1, 0, 0] : Fin 3 → ℝ)
              - (Real.sin (Real.pi / 2) * Real.sin (Real.pi / 2))
                  • crossProduct ![1, 0, 0] ![0, 0, 1]) := sorry

end AxQM.Concrete
