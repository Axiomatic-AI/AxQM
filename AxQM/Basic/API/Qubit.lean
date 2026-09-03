/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.Observable
import AxQM.Concrete.Pauli
import AxQM.Concrete.PauliOuterProduct
import AxQM.Concrete.PauliEigenvectors
import AxQM.ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM

/-!
# AxQM.Basic.API — the qubit and its Pauli vector observables

The operator-level form of the two-level system and its spin observables.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **qubit**: the two-level quantum system, whose state space is the standard
two-dimensional complex Hilbert space `EuclideanSpace ℂ (Fin 2)`. -/
def qubit : QSystem := QSystem.ofModel (EuclideanSpace ℂ (Fin 2))

/-- **The qubit state space is nontrivial** (it is `EuclideanSpace ℂ (Fin 2)`, dimension `2`). -/
instance : Nontrivial qubit.space :=
  inferInstanceAs (Nontrivial (EuclideanSpace ℂ (Fin 2)))

/-- **The qubit has dimension `2`**: `finrank ℂ qubit.space = 2`. -/
theorem finrank_qubit_space : Module.finrank ℂ qubit.space = 2 := by
  change Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) = 2
  exact finrank_euclideanSpace_fin

/-- The **computational basis state `|0⟩ = (1, 0)`** as a pure state of the qubit — the standard
basis ket `Concrete.ket 0` viewed in `EuclideanSpace`. -/
def qubitKet0 : PureState qubit where
  vec := WithLp.toLp 2 (Concrete.ket 0)
  normalized := by
    have h : ‖(WithLp.toLp 2 (Concrete.ket 0) : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp [Concrete.ket, Fin.sum_univ_two]
    exact h

/-- The **Pauli vector observable** `n · σ = n₀ X + n₁ Y + n₂ Z` on the qubit, for a real
three-vector `n`. These are the observables `Q, R, S, T` of Nielsen & Chuang Problem 2.3. -/
def pauliObservable (n : Fin 3 → ℝ) : Observable qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.pauliDot n)
  selfAdjoint :=
    (Concrete.pauliDot_isHermitian n).isSelfAdjoint.map
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))

/-- The underlying operator of `pauliObservable n` is the `Matrix.toEuclideanCLM` image of the
concrete matrix `Concrete.pauliDot n`. -/
@[simp]
theorem pauliObservable_op (n : Fin 3 → ℝ) :
    (pauliObservable n).op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.pauliDot n) :=
  rfl

/-- **The Pauli vector observable of a unit vector is an involution:** `(n · σ)² = 1` in the qubit's
operator ring, for a unit vector `n` (`n₀² + n₁² + n₂² = 1`). -/
theorem pauliObservable_op_mul_self {n : Fin 3 → ℝ}
    (h : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    (pauliObservable n).op * (pauliObservable n).op = 1 := by
  -- The operator multiplication lives at `↑qubit →L ↑qubit`; restate it at the definitionally
  -- equal `EuclideanSpace ℂ (Fin 2) →L …` so the `⋆`-algebra homomorphism lemmas apply.
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.pauliDot n)
       * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.pauliDot n) = 1
  rw [← map_mul, Concrete.pauliDot_mul_self_of_unit h, map_one]

/-- The **computational-basis pure state** `|i⟩` of the qubit. Instantiating `i = 0` / `i = 1` gives
the states `|0⟩` and `|1⟩` of Chapter 2. -/
def qubitBasis (i : Fin 2) : PureState qubit where
  vec := EuclideanSpace.single i 1
  normalized := by
    change ‖EuclideanSpace.single i (1 : ℂ)‖ = 1
    simp

/-- The underlying unit vector of the computational-basis state `|i⟩` is `EuclideanSpace.single
i 1`. -/
@[simp]
theorem qubitBasis_vec (i : Fin 2) :
    (qubitBasis i).vec = EuclideanSpace.single i 1 := rfl

/-- The **Pauli `X` observable** on the qubit: the Pauli vector observable `n · σ` for the unit
direction `n = (1, 0, 0)`, i.e. `X = pauliObservable ![1, 0, 0]`. -/
def pauliXObservable : Observable qubit := pauliObservable ![1, 0, 0]

/-- The operator of the Pauli `X` observable is `Matrix.toEuclideanCLM Concrete.pauliX`: the
Pauli direction `(1, 0, 0)` collapses `Concrete.pauliDot ![1, 0, 0]` to the concrete matrix
`Concrete.pauliX = !![0, 1; 1, 0]`. -/
@[simp]
theorem pauliXObservable_op :
    pauliXObservable.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX := by
  rw [pauliXObservable, pauliObservable_op]
  congr 1
  rw [Concrete.pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Concrete.pauliX]

/-- **`X² = 1`:** the Pauli `X` observable is an involution in the qubit's operator ring. -/
theorem pauliXObservable_op_mul_self :
    pauliXObservable.op * pauliXObservable.op = 1 := by
  rw [pauliXObservable]
  exact pauliObservable_op_mul_self
    (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons])

/-- The **Pauli `Y` observable** on the qubit: the Pauli vector observable `n · σ` for the unit
direction `n = (0, 1, 0)`, i.e. `Y = pauliObservable ![0, 1, 0]`. -/
def pauliYObservable : Observable qubit := pauliObservable ![0, 1, 0]

/-- The operator of the Pauli `Y` observable is `Matrix.toEuclideanCLM Concrete.pauliY`: the Pauli
direction `(0, 1, 0)` collapses `Concrete.pauliDot ![0, 1, 0]` to the concrete matrix
`Concrete.pauliY = !![0, -i; i, 0]`. -/
@[simp]
theorem pauliYObservable_op :
    pauliYObservable.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliY := by
  rw [pauliYObservable, pauliObservable_op]
  congr 1
  rw [Concrete.pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Concrete.pauliY]

/-- The **Pauli `Z` observable** on the qubit: the Pauli vector observable `n · σ` for the unit
direction `n = (0, 0, 1)`, i.e. `Z = pauliObservable ![0, 0, 1]`. -/
def pauliZObservable : Observable qubit := pauliObservable ![0, 0, 1]

/-- The operator of the Pauli `Z` observable is `Matrix.toEuclideanCLM Concrete.pauliZ`: the Pauli
direction `(0, 0, 1)` collapses `Concrete.pauliDot ![0, 0, 1]` to the concrete matrix
`Concrete.pauliZ = !![1, 0; 0, -1]`. -/
@[simp]
theorem pauliZObservable_op :
    pauliZObservable.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliZ := by
  rw [pauliZObservable, pauliObservable_op]
  congr 1
  rw [Concrete.pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Concrete.pauliZ]

/-- **`Z² = 1`:** the Pauli `Z` observable is an involution in the qubit's operator ring. -/
theorem pauliZObservable_op_mul_self :
    pauliZObservable.op * pauliZObservable.op = 1 := by
  rw [pauliZObservable]
  exact pauliObservable_op_mul_self
    (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons])

/-- **`Y² = 1`:** the Pauli `Y` observable is an involution in the qubit's operator ring. -/
theorem pauliYObservable_op_mul_self :
    pauliYObservable.op * pauliYObservable.op = 1 := by
  rw [pauliYObservable]
  exact pauliObservable_op_mul_self
    (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons])

/-- **Applying `Z` to a `toLp` vector is `Z *ᵥ`:** `Z (toLp v) = toLp (Concrete.pauliZ *ᵥ v)`. -/
theorem pauliZObservable_apply_toLp (v : Fin 2 → ℂ) :
    pauliZObservable.op (WithLp.toLp 2 v) = WithLp.toLp 2 (Concrete.pauliZ.mulVec v) := by
  rw [pauliZObservable_op]; exact Matrix.toEuclideanCLM_toLp Concrete.pauliZ v

/-- `Z |0⟩ = |0⟩`: `Z`'s `+1` operator eigenvalue equation on `Concrete.ket 0`. -/
theorem pauliZObservable_apply_ket0 :
    pauliZObservable.op (WithLp.toLp 2 (Concrete.ket 0))
      = (1 : ℂ) • WithLp.toLp 2 (Concrete.ket 0) := by
  rw [pauliZObservable_apply_toLp, Concrete.pauliZ_mulVec_ket_zero, WithLp.toLp_smul]

/-- `Z |1⟩ = -|1⟩`: `Z`'s `-1` operator eigenvalue equation on `Concrete.ket 1`. -/
theorem pauliZObservable_apply_ket1 :
    pauliZObservable.op (WithLp.toLp 2 (Concrete.ket 1))
      = ((-1 : ℝ) : ℂ) • WithLp.toLp 2 (Concrete.ket 1) := by
  rw [pauliZObservable_apply_toLp, Concrete.pauliZ_mulVec_ket_one, WithLp.toLp_smul,
    Complex.ofReal_neg, Complex.ofReal_one]

/-- **`Z |i⟩ = (-1)ⁱ |i⟩`** at the observable operator level: the Pauli `Z` observable acts on the
computational-basis ket `|i⟩` by the eigenvalue `(-1)ⁱ`. -/
theorem pauliZObservable_op_apply_qubitBasis (i : Fin 2) :
    pauliZObservable.op (qubitBasis i).vec = (-1 : ℂ) ^ (i : ℕ) • (qubitBasis i).vec := by
  fin_cases i
  · simpa using pauliZObservable_apply_ket0
  · simpa using pauliZObservable_apply_ket1

/-- **Orthonormality of the computational basis:** `⟨i|j⟩ = δᵢⱼ`. The inner product of the
computational-basis states `|i⟩`, `|j⟩` of the qubit is `1` when `i = j` and `0` otherwise. -/
theorem qubitBasis_inner_qubitBasis (i j : Fin 2) :
    inner ℂ (qubitBasis i).vec (qubitBasis j).vec = if i = j then (1 : ℂ) else 0 := by
  change inner ℂ (EuclideanSpace.single i (1 : ℂ)) (EuclideanSpace.single j (1 : ℂ)) = _
  rw [EuclideanSpace.inner_single_left]
  simp [PiLp.single_apply]

/-- **The qubit computational basis is orthonormal** as a family of state vectors. -/
theorem qubitBasis_vec_orthonormal : Orthonormal ℂ (fun i => (qubitBasis i).vec) :=
  orthonormal_iff_ite.mpr qubitBasis_inner_qubitBasis

/-- **The computational basis `|0⟩, |1⟩` as a `ℂ`-basis of the qubit state space.** -/
noncomputable def qubitModuleBasis : Module.Basis (Fin 2) ℂ qubit.space :=
  basisOfLinearIndependentOfCardEqFinrank
    qubitBasis_vec_orthonormal.linearIndependent
    (by rw [Fintype.card_fin, finrank_qubit_space])

/-- The `i`-th vector of `qubitModuleBasis` is the computational ket `|i⟩`, `(qubitBasis i).vec`. -/
@[simp] theorem qubitModuleBasis_apply (i : Fin 2) :
    qubitModuleBasis i = (qubitBasis i).vec :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i

/-- **The computational basis `qubitModuleBasis` is orthonormal.** -/
theorem qubitModuleBasis_orthonormal : Orthonormal ℂ ⇑qubitModuleBasis := by
  rw [show (⇑qubitModuleBasis) = (fun i => (qubitBasis i).vec) from funext qubitModuleBasis_apply]
  exact qubitBasis_vec_orthonormal

/-- The Pauli `Z` observable is **traceless**: `tr Z = 0`. -/
theorem trace_pauliZObservable : LinearMap.trace ℂ qubit.space ↑pauliZObservable.op = 0 := by
  rw [pauliZObservable_op]; exact (Matrix.trace_toEuclideanCLM _).trans Concrete.pauliZ_trace

end AxQM
