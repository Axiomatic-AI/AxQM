/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.GroverRotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Concrete: iterating the Grover search

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §6.1.3–6.1.4 (pp. 252–254) analyse
the quantum search algorithm. Exercise 6.4 asks to give the explicit steps of that algorithm for the
**multiple-solution** case `1 < M < N/2` (the boxed `M = 1` "Algorithm: Quantum search" on p. 254
being the special case). This file works over the two-dimensional `|α⟩, |β⟩` plane in which the
whole geometric picture lives.

## Contents

* `planeState φ` — the unit vector `cos φ |α⟩ + sin φ |β⟩` at angle `φ` from `|α⟩` in the plane
  `span{|α⟩, |β⟩}` (with `|α⟩ = stdVec 0`, `|β⟩ = stdVec 1`); `groverState θ = planeState (θ/2)`
  (`groverState_eq_planeState`).
* `groverRotation_mulVec_planeState` — the rotation acts on a plane state by adding to its angle:
  `G · (cos φ |α⟩ + sin φ |β⟩) = cos(φ+θ) |α⟩ + sin(φ+θ) |β⟩`.
* `groverIteration_pow_mulVec_groverState` — **N&C Eq. 6.12**: `k` Grover iterations rotate the
  starting state `|ψ⟩` (at `θ/2`) to `cos((2k+1)θ/2) |α⟩ + sin((2k+1)θ/2) |β⟩`.
-/

namespace AxQM.Concrete

open Matrix

/-- **The plane state at angle `φ`**: the unit vector `cos φ |α⟩ + sin φ |β⟩` of `ℂ²`, at angle `φ`
from `|α⟩` in the plane `span{|α⟩, |β⟩}` (with `|α⟩ = stdVec 0`, `|β⟩ = stdVec 1`). The generic
point of N&C's geometric picture (§6.1.3). -/
noncomputable def planeState (φ : ℝ) : Fin 2 → ℂ :=
  (Real.cos φ : ℂ) • stdVec 0 + (Real.sin φ : ℂ) • stdVec 1

@[simp] theorem planeState_apply_zero (φ : ℝ) : planeState φ 0 = (Real.cos φ : ℂ) := by
  simp [planeState, stdVec]

@[simp] theorem planeState_apply_one (φ : ℝ) : planeState φ 1 = (Real.sin φ : ℂ) := by
  simp [planeState, stdVec]

/-- The Grover starting state `|ψ⟩` is the plane state at angle `θ/2` (N&C Eq. 6.10). -/
theorem groverState_eq_planeState (θ : ℝ) : groverState θ = planeState (θ / 2) := rfl

/-- **The rotation acts on a plane state by adding its angle** (N&C §6.1.3): the Grover rotation
matrix sends `cos φ |α⟩ + sin φ |β⟩` to `cos(φ+θ) |α⟩ + sin(φ+θ) |β⟩`. -/
theorem groverRotation_mulVec_planeState (θ φ : ℝ) :
    groverRotation θ *ᵥ planeState φ = planeState (φ + θ) := by
  have hc : (Real.cos (φ + θ) : ℂ)
      = (Real.cos θ : ℂ) * (Real.cos φ : ℂ) - (Real.sin θ : ℂ) * (Real.sin φ : ℂ) := by
    rw [Real.cos_add]; push_cast; ring
  have hs : (Real.sin (φ + θ) : ℂ)
      = (Real.sin θ : ℂ) * (Real.cos φ : ℂ) + (Real.cos θ : ℂ) * (Real.sin φ : ℂ) := by
    rw [Real.sin_add]; push_cast; ring
  funext i
  fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, groverRotation, planeState_apply_zero,
      planeState_apply_one, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
      Fin.zero_eta, Fin.mk_one] <;>
    first
      | linear_combination -hc
      | linear_combination -hs

/-- **Iterating the rotation** `k` times rotates a plane state by `k·θ`:
`Gᵏ · (cos φ |α⟩ + sin φ |β⟩) = cos(φ + kθ) |α⟩ + sin(φ + kθ) |β⟩`. -/
theorem groverRotation_pow_mulVec_planeState (θ φ : ℝ) (k : ℕ) :
    (groverRotation θ) ^ k *ᵥ planeState φ = planeState (φ + k * θ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, groverRotation_mulVec_planeState]
    congr 1
    push_cast
    ring

/-- **Nielsen & Chuang, Eq. 6.12.** After `k` Grover iterations the starting state `|ψ⟩` (at angle
`θ/2` from `|α⟩`) has been rotated to `cos((2k+1)θ/2) |α⟩ + sin((2k+1)θ/2) |β⟩` — it sits at angle
`(2k+1)θ/2`, rotating by `θ` per iteration towards the all-solutions vector `|β⟩` (at `π/2`). -/
theorem groverIteration_pow_mulVec_groverState (θ : ℝ) (k : ℕ) :
    (groverIteration θ) ^ k *ᵥ groverState θ = planeState ((2 * k + 1) * θ / 2) := by
  rw [groverState_eq_planeState, groverIteration_eq_rotation, groverRotation_pow_mulVec_planeState]
  congr 1
  ring

end AxQM.Concrete
