/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Evolution
import AxQM.ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl

/-!
# AxQM.Basic.API — the `d`-level system (qudit) and diagonal phase gates

The operator-level form of a finite `d`-level system and the diagonal (phase) unitaries on
it — a concrete model generalizing the qubit (`qubit = qudit 2`) to arbitrary dimension. It
is the register model used by the circuit constructions of Nielsen & Chuang, Chapter 4
(e.g. Problem 4.1's input and ancilla registers of dimension `2^m` / `2^n`).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **`d`-level quantum system (qudit)**: the system whose state space is the standard
`d`-dimensional complex Hilbert space `EuclideanSpace ℂ (Fin d)`. The qubit is `qudit 2`;
`qudit (2^n)` is an `n`-qubit register. -/
def qudit (d : ℕ) : QSystem := QSystem.ofModel (EuclideanSpace ℂ (Fin d))

@[simp]
theorem qudit_space (d : ℕ) : (qudit d).space = EuclideanSpace ℂ (Fin d) := rfl

/-- The state space of `qudit d` is nontrivial when `d ≥ 1` (it contains the computational-basis
vectors `|i⟩`). Supplies the `Nontrivial S.space` hypothesis that state constructions such as the
maximally mixed state `I/d` require. -/
instance qudit_space_nontrivial {d : ℕ} [NeZero d] : Nontrivial (qudit d).space := by
  rw [qudit_space]; infer_instance

/-- **The qudit has dimension `d`**: `finrank ℂ (qudit d).space = d`, since `(qudit d).space` is
`EuclideanSpace ℂ (Fin d)`. -/
theorem finrank_qudit (d : ℕ) : Module.finrank ℂ (qudit d).space = d := by
  change Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) = d
  exact finrank_euclideanSpace_fin

/-- The **computational-basis pure state** `|i⟩` of `qudit d`: the standard basis vector
`EuclideanSpace.single i 1`, normalized because `‖EuclideanSpace.single i 1‖ = ‖(1 : ℂ)‖ = 1`. -/
def quditBasis {d : ℕ} (i : Fin d) : PureState (qudit d) where
  vec := EuclideanSpace.single i 1
  normalized := by
    change ‖EuclideanSpace.single i (1 : ℂ)‖ = 1
    simp

@[simp]
theorem quditBasis_vec {d : ℕ} (i : Fin d) :
    (quditBasis i).vec = EuclideanSpace.single i 1 := rfl

/-- The **computational basis of `qudit d` is orthonormal** (`⟨i|j⟩ = δᵢⱼ`), being the standard
`EuclideanSpace.single` basis (`EuclideanSpace.orthonormal_single`). -/
theorem quditBasis_orthonormal (d : ℕ) :
    Orthonormal ℂ (fun i : Fin d => (quditBasis i).vec) := by
  simp only [quditBasis_vec]
  exact EuclideanSpace.orthonormal_single

/-- **Inner product of two computational-basis states** (orthonormality in δ-form):
`⟨x, y⟩ = δₓᵧ`, i.e. `1` if `x = y` and `0` otherwise. The δ-form of `quditBasis_orthonormal`, the
citable input to every amplitude computation over the computational basis. -/
theorem quditBasis_inner {d : ℕ} (x y : Fin d) :
    inner ℂ (quditBasis x).vec (quditBasis y).vec = if x = y then (1 : ℂ) else 0 :=
  orthonormal_iff_ite.mp (quditBasis_orthonormal d) x y

/-- The **diagonal phase gate** `D = diag(e^{iθ₀}, …, e^{iθ_{d-1}})` on `qudit d`, for a real angle
vector `θ : Fin d → ℝ`, as a unitary `Evolution`. This is the phase layer used in the
computable-phase-shift circuit. -/
def diagPhase {d : ℕ} (θ : Fin d → ℝ) : Evolution (qudit d) where
  op := (EuclideanSpace.basisFun (Fin d) ℂ).diagonalOperator
          (fun i => Complex.exp ((θ i : ℂ) * Complex.I))
  unitary := by
    change (EuclideanSpace.basisFun (Fin d) ℂ).diagonalOperator
        (fun i => Complex.exp ((θ i : ℂ) * Complex.I))
        ∈ unitary (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    exact OrthonormalBasis.diagonalOperator_mem_unitary _ _ (fun i => by simp [Complex.norm_exp])

/-- **Action of a computational-basis diagonal operator on a standard basis vector:**
`(basisFun.diagonalOperator w)|i⟩ = wᵢ|i⟩`, since `|i⟩ = EuclideanSpace.basisFun … i`. -/
theorem basisFun_diagonalOperator_apply_single {d : ℕ} (w : Fin d → ℂ) (i : Fin d) :
    (EuclideanSpace.basisFun (Fin d) ℂ).diagonalOperator w (EuclideanSpace.single i 1)
      = w i • EuclideanSpace.single i (1 : ℂ) := by
  rw [← EuclideanSpace.basisFun_apply, OrthonormalBasis.diagonalOperator_apply_self]

end AxQM
