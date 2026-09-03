/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.PauliTrotter
import AxQM.Basic.API.Eigenstate
import AxQM.Concrete.PauliStringStdInvolution
import AxQM.Basic.API.Evolution
import AxQM.ToMathlib.Analysis.Normed.Algebra.ExponentialInvolution

/-!
# an involutive observable is a controllable unitary (`Observable.toEvolution`)

The bridge that turns an **involutive
observable** — a self-adjoint operator `A` with `A² = I`, i.e. a Hermitian operator with eigenvalues
`±1` — into an `Evolution` (a unitary), so it can be *controlled*. This is exactly the promotion
Nielsen & Chuang invoke for Figure 10.13: the measurement circuit `(H ⊗ 1) · C(U) · (H ⊗ 1)` needs
its measured operator as a controllable unitary `U`, and "`M` is an arbitrary Hermitian operator
with eigenvalues `±1`" — products of Pauli operators included. The stabilizer syndrome circuits of
§10.5.8 feed each stabilizer generator through this bridge.

## Main declarations
* `Observable.toEvolution` — the bridge: from `A : Observable S` and a proof `A.op * A.op = 1`,
  the `Evolution S` with operator `A.op`. Unitarity is immediate: `A` self-adjoint means
  `star A.op = A.op`, so `star A.op * A.op = A.op * A.op = 1` and likewise on the other side.
* `pauliStringHamiltonian_op_mul_self` — the honest (phase `+1`) Pauli-string observable
  `pauliStringHamiltonian g 1` is an involution: `(P_g)² = I`, from the matrix fact
  `Concrete.pauliStringStd_mul_self` through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`.
-/

open scoped Matrix

namespace AxQM

variable {S : QSystem}

/-- **An involutive observable is a unitary evolution.** Given `A : Observable S` with `A² = I`
(`hA : A.op * A.op = 1`), the operator `A.op` is unitary — it is self-adjoint, so
`star A.op = A.op` and `star A.op * A.op = A.op * A.op = 1`, and symmetrically `A.op * star A.op =
1`. Hence `A` promotes to an `Evolution` with the same operator. This is the "`M` is Hermitian with
eigenvalues `±1`, so `C(M)` makes sense" step of the Figure-10.13 operator-measurement circuit. -/
def Observable.toEvolution (A : Observable S) (hA : A.op * A.op = 1) : Evolution S where
  op := A.op
  unitary := by
    rw [Unitary.mem_iff]
    have hsa : star A.op = A.op := A.selfAdjoint
    rw [hsa]
    exact ⟨hA, hA⟩

/-- **An honest Pauli-string observable is an involution**: `(P_g)² = I` for `P_g =
pauliStringHamiltonian g 1`. -/
theorem pauliStringHamiltonian_op_mul_self {n : ℕ} (g : Fin n → Fin 4) :
    (pauliStringHamiltonian g 1).op * (pauliStringHamiltonian g 1).op = 1 := by
  unfold pauliStringHamiltonian
  simp only [Complex.ofReal_one, one_smul]
  -- `erw` bridges the definitional coercion between `(qudit (2^n)).space` and `EuclideanSpace ℂ _`.
  erw [← map_mul Matrix.toEuclideanCLM, Concrete.pauliStringStd_mul_self]
  exact map_one Matrix.toEuclideanCLM

end AxQM
