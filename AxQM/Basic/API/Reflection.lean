/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Basic.API.Evolution

/-!
# AxQM.Basic.API — the state reflection `R_ψ = I − 2|ψ⟩⟨ψ|`

For a pure state `ψ`, the unitary that flips the phase of `|ψ⟩` and fixes its orthogonal
complement (Nielsen & Chuang, Problem 6.2, generalized quantum searching).
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The state reflection** `R_ψ = I − 2|ψ⟩⟨ψ|` of Nielsen & Chuang, Problem 6.2, as a
closed-system `Evolution`. It flips the phase of `|ψ⟩` (`R_ψ|ψ⟩ = −|ψ⟩`) and fixes every state
orthogonal to `|ψ⟩`. -/
def reflectionEvolution (ψ : PureState S) : Evolution S where
  op := 1 - (2 : ℂ) • rankOne ℂ ψ.vec ψ.vec
  unitary := by
    have hself : inner ℂ ψ.vec ψ.vec = (1 : ℂ) := inner_self_eq_one_of_norm_eq_one ψ.normalized
    set P : S.space →L[ℂ] S.space := rankOne ℂ ψ.vec ψ.vec with hPdef
    have hPP : P * P = P := by
      rw [hPdef, ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hself, one_smul]
    have hPsa : star P = P := by
      rw [hPdef, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]
    have hRsa : star (1 - (2 : ℂ) • P) = 1 - (2 : ℂ) • P := by
      rw [star_sub, star_one, star_smul, hPsa, star_ofNat]
    have hRR : (1 - (2 : ℂ) • P) * (1 - (2 : ℂ) • P) = 1 := by
      simp only [mul_sub, sub_mul, one_mul, mul_one, smul_mul_smul_comm, hPP]
      module
    rw [Unitary.mem_iff, hRsa]
    exact ⟨hRR, hRR⟩

end AxQM
