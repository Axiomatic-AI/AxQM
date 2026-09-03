/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Concrete: single-qubit process tomography, the amplitude-damping χ matrix (N&C Ex 8.35)

Explicit `2 × 2` / `4 × 4` complex matrices and one matrix identity, formalizing the single-qubit
quantum-process-tomography computation of Nielsen & Chuang, *Quantum Computation and Quantum
Information*, **Box 8.5** (p. 393) and the worked **Exercise 8.35** (p. 394).

## Exercise 8.35 — the amplitude-damping example

* `ampDampMeasuredBlock γ` — the block `[[ρ'₁, ρ'₂], [ρ'₃, ρ'₄]]` of the four measured matrices.
* `ampDampChiMatrix γ` — the χ matrix the exercise asks for.
* `ampDampChiMatrix_eq` — `singleQubitProcessChi (ampDampMeasuredBlock γ) =
  ampDampChiMatrix γ`, i.e. the Box 8.5 product `Λ ρ' Λ` equals the stated `χ` (for `γ ≤ 1`).
-/

open Matrix Complex

namespace AxQM.Concrete

/-- The fixed single-qubit process-tomography matrix `Λ = ½[[I, X], [X, -I]]` of Nielsen & Chuang,
Box 8.5 (eq. 8.178): a `4 × 4` matrix written in `2 × 2` blocks, with the identity and Pauli `X` in
the corners. It lets the process matrix be recovered by the block product `χ = Λ ρ' Λ`. The
`4 × 4` block index is modelled as `Fin 2 ⊕ Fin 2`. -/
noncomputable def processTomographyΛ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks ((1 / 2 : ℂ) • 1) ((1 / 2 : ℂ) • pauliX) ((1 / 2 : ℂ) • pauliX)
    ((1 / 2 : ℂ) • (-1))

/-- The Box 8.5 process-matrix reconstruction (eq. 8.179): from the `4 × 4` block `ρ'` of measured
output density matrices, the χ matrix of a single-qubit operation is `χ = Λ ρ' Λ`, with
`Λ = processTomographyΛ`. -/
noncomputable def singleQubitProcessChi
    (rho' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  processTomographyΛ * rho' * processTomographyΛ

/-- The `4 × 4` block `ρ' = [[ρ'₁, ρ'₂], [ρ'₃, ρ'₄]]` of the four density matrices measured from the
amplitude-damping black box of Nielsen & Chuang, Exercise 8.35 (eqs. 8.182–8.185): `ρ'₁ = [[1,0],
[0,0]]` (`|0⟩` is left invariant), `ρ'₂ = [[0,√(1-γ)],[0,0]]` and `ρ'₃ = [[0,0],[√(1-γ),0]]`
(superpositions are damped), `ρ'₄ = [[γ,0],[0,1-γ]]` (`|1⟩` partially decays to `|0⟩`). -/
noncomputable def ampDampMeasuredBlock (γ : ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks
    !![1, 0; 0, 0]
    !![0, (Real.sqrt (1 - γ) : ℂ); 0, 0]
    !![0, 0; (Real.sqrt (1 - γ) : ℂ), 0]
    !![(γ : ℂ), 0; 0, ((1 - γ : ℝ) : ℂ)]

/-- The χ matrix determined for the amplitude-damping black box of Nielsen & Chuang, Exercise 8.35,
written as a `4 × 4` matrix in `2 × 2` blocks:
`χ = ¼[[(1+√(1-γ))², 0, 0, γ], [0, γ, -γ, 0], [0, -γ, γ, 0], [γ, 0, 0, (1-√(1-γ))²]]`. -/
noncomputable def ampDampChiMatrix (γ : ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  (1 / 4 : ℂ) • Matrix.fromBlocks
    !![(1 + (Real.sqrt (1 - γ) : ℂ)) ^ 2, 0; 0, (γ : ℂ)]
    !![0, (γ : ℂ); -(γ : ℂ), 0]
    !![0, -(γ : ℂ); (γ : ℂ), 0]
    !![(γ : ℂ), 0; 0, (1 - (Real.sqrt (1 - γ) : ℂ)) ^ 2]

/-- **Nielsen & Chuang, Exercise 8.35 (determine the χ matrix).** Applying the Box 8.5 process
formula `χ = Λ ρ' Λ` to the four measured density matrices of the amplitude-damping black box
yields the stated χ matrix: `singleQubitProcessChi (ampDampMeasuredBlock γ) = ampDampChiMatrix
γ`, for `γ ≤ 1`. -/
theorem ampDampChiMatrix_eq (γ : ℝ) (hγ : γ ≤ 1) :
    singleQubitProcessChi (ampDampMeasuredBlock γ) = ampDampChiMatrix γ := sorry

end AxQM.Concrete
