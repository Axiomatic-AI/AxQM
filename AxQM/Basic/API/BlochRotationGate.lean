/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PiEighthGate
import AxQM.Basic.API.BlochState
import AxQM.Concrete.Rotation
import AxQM.Concrete.BlochRotation

/-!
# AxQM.Basic.API — the axis rotation gate `R_n̂(θ)` as a qubit evolution

The operator-level form of the single-qubit rotation about an arbitrary axis, Nielsen & Chuang
eq. 4.8: the rotation `R_n̂(θ) = exp(−iθ n̂·σ/2)` promoted from its concrete `2 × 2` unitary matrix
`Concrete.rotAxis n θ` to an `Evolution` of the `qubit`.
-/

noncomputable section

namespace AxQM

/-- The **axis rotation gate** `R_n̂(θ) = exp(−iθ n̂·σ/2)` as a closed-system evolution of the
`qubit` (Nielsen & Chuang, eq. 4.8), for an arbitrary three-vector `n`. -/
def rotAxisGate (n : Fin 3 → ℝ) (θ : ℝ) : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotAxis n θ)
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))
      (Concrete.rotAxis_mem_unitaryGroup n θ)

/-- **Nielsen & Chuang, Exercise 4.6 — the Bloch-sphere interpretation of rotations.** For a unit
axis `n̂` (`hn`), evolving the Bloch state `blochState v` — the qubit density operator `½(I +
v·σ)` — by the rotation gate `rotAxisGate n̂ θ = R_n̂(θ)` rotates its Bloch vector `v` by the
angle `θ` about `n̂`: `(rotAxisGate n̂ θ).evolve (blochState v) = blochState (Concrete.rot3D n̂
θ v)`.

The rotated vector stays in the Bloch ball, so the right-hand `blochState` is well defined; that
bound is its second argument.

The unit-axis hypothesis `hn` is genuine (N&C's `n̂` is the rotation *axis*); `θ` and the Bloch
vector `v` are fully general.
-/
theorem rotAxisGate_evolve_blochState {n : Fin 3 → ℝ}
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (θ : ℝ) (v : Fin 3 → ℝ)
    (h : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 ≤ 1) :
    (rotAxisGate n θ).evolve (blochState v h)
      = blochState (Concrete.rot3D n θ v) ((Concrete.rot3D_sq_sum hn θ v).trans_le h) := sorry

end AxQM
