/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Trace
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Adjoint
public import AxQM.ToMathlib.Analysis.InnerProductSpace.LinearMap
public import AxQM.ToMathlib.Analysis.InnerProductSpace.TensorProduct
public import AxQM.ToMathlib.Analysis.InnerProductSpace.Trace

/-!
# Abstract partial trace on a tensor product

For finite-dim inner product spaces `E`, `F` over `RCLike 𝕜`, given an orthonormal basis
`b : OrthonormalBasis ι 𝕜 F` on the right factor, the partial trace over `F` of a linear
operator `T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F` is the operator `partialTraceRight b T : E →ₗ[𝕜] E`
given by `∑ k, restrictRight b k ∘ₗ T ∘ₗ embedRight b k`.

## Main definitions

* `LinearMap.embedRight`, `LinearMap.restrictRight`: the basis-aware embed/restrict maps.
* `LinearMap.partialTraceRight`: partial trace over the right factor (basis-parametric).
* Symmetric `*Left` versions.

## Main results

* `LinearMap.partialTraceRight_apply`: point-applied form of `partialTraceRight`.
* `LinearMap.partialTraceRight_tensorMap`: the canonical identity
  `partialTraceRight b (TensorProduct.map A B) = (LinearMap.trace 𝕜 _ B) • A` for an OB `b` on F.
* `LinearMap.trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight` (and the `…Left` analogue):
  the trace-level partial-trace duality
  `trace (map V id ∘ₗ T) = trace (V ∘ₗ partialTraceRight b T)`.
* `LinearMap.partialTraceRight_eq_of_basis` (and the `…Left` analogue): basis-independence of the
  partial trace.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

variable {ι₂ : Type*} [Fintype ι₂]

/-- The "embed into the right factor at `b k`" map: `x ↦ x ⊗ₜ b k`. -/
noncomputable def embedRight (b : OrthonormalBasis ι₂ 𝕜 F) (k : ι₂) : E →ₗ[𝕜] E ⊗[𝕜] F :=
  (TensorProduct.mk 𝕜 E F).flip (b k)

@[simp]
theorem embedRight_apply (b : OrthonormalBasis ι₂ 𝕜 F) (k : ι₂) (x : E) :
    embedRight b k x = x ⊗ₜ[𝕜] b k := rfl

/-- The "restrict at the `b k` slot of the right factor" map:
`x ⊗ₜ y ↦ ⟨b k, y⟩_F • x`, extended linearly. -/
noncomputable def restrictRight (b : OrthonormalBasis ι₂ 𝕜 F) (k : ι₂) :
    E ⊗[𝕜] F →ₗ[𝕜] E :=
  (TensorProduct.rid 𝕜 E).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (innerSL 𝕜 (b k)).toLinearMap

@[simp]
theorem restrictRight_tmul (b : OrthonormalBasis ι₂ 𝕜 F) (k : ι₂) (x : E) (y : F) :
    restrictRight b k (x ⊗ₜ[𝕜] y) = ⟪b k, y⟫_𝕜 • x := rfl

/-- The partial trace of `T : E ⊗ F →ₗ E ⊗ F` over the right factor, parametrized by an OB
on `F`. Defined as `∑ k, restrictRight b k ∘ₗ T ∘ₗ embedRight b k`. -/
noncomputable def partialTraceRight (b : OrthonormalBasis ι₂ 𝕜 F)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) : E →ₗ[𝕜] E :=
  ∑ k : ι₂, restrictRight b k ∘ₗ T ∘ₗ embedRight b k

theorem partialTraceRight_eq_sum (b : OrthonormalBasis ι₂ 𝕜 F)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceRight b T = ∑ k : ι₂, restrictRight b k ∘ₗ T ∘ₗ embedRight b k :=
  rfl

theorem partialTraceRight_apply (b : OrthonormalBasis ι₂ 𝕜 F)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) (x : E) :
    partialTraceRight b T x = ∑ k : ι₂, restrictRight b k (T (x ⊗ₜ[𝕜] b k)) := by
  simp [partialTraceRight_eq_sum, LinearMap.sum_apply, LinearMap.comp_apply]

/-- The partial trace of `TensorProduct.map A B` over the right factor
equals `(trace B) • A`. -/
theorem partialTraceRight_tensorMap [FiniteDimensional 𝕜 F]
    (b : OrthonormalBasis ι₂ 𝕜 F) (A : E →ₗ[𝕜] E) (B : F →ₗ[𝕜] F) :
    partialTraceRight b (TensorProduct.map A B) = (LinearMap.trace 𝕜 _ B) • A := by
  ext x
  simp only [partialTraceRight_apply, TensorProduct.map_tmul, restrictRight_tmul,
    LinearMap.smul_apply, ← Finset.sum_smul]
  rw [← LinearMap.trace_eq_sum_inner B b]

/-- **Bundled `partialTraceRight` as a `LinearMap`**: the partial trace over the right factor,
viewed as a linear map `(E ⊗ F →ₗ E ⊗ F) →ₗ (E →ₗ E)`. -/
noncomputable def partialTraceRightLM (b : OrthonormalBasis ι₂ 𝕜 F) :
    (E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) →ₗ[𝕜] (E →ₗ[𝕜] E) where
  toFun := partialTraceRight b
  map_add' T₁ T₂ := by
    simp only [partialTraceRight_eq_sum, LinearMap.add_comp, LinearMap.comp_add,
      Finset.sum_add_distrib]
  map_smul' c T := by
    simp only [partialTraceRight_eq_sum, RingHom.id_apply, LinearMap.smul_comp,
      LinearMap.comp_smul, Finset.smul_sum]

@[simp]
theorem partialTraceRightLM_apply (b : OrthonormalBasis ι₂ 𝕜 F)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceRightLM b T = partialTraceRight b T := rfl

/-- **Partial-trace-of-rank-one-pure-tensor identity** (right slot, abstract): for any
pure-tensor inputs `a₁ ⊗ b₁` and `a₂ ⊗ b₂` in `E ⊗ F`,
`partialTraceRight b (rankOne (a₁ ⊗ b₁) (a₂ ⊗ b₂)) = ⟪b₂, b₁⟫ • rankOne a₁ a₂`. -/
theorem partialTraceRight_rankOne_tmul (b : OrthonormalBasis ι₂ 𝕜 F)
    (a₁ a₂ : E) (b₁ b₂ : F) :
    partialTraceRight b ((InnerProductSpace.rankOne 𝕜 (a₁ ⊗ₜ[𝕜] b₁ : E ⊗[𝕜] F)
        (a₂ ⊗ₜ[𝕜] b₂)).toLinearMap) =
      ⟪b₂, b₁⟫_𝕜 • ((InnerProductSpace.rankOne 𝕜 a₁ a₂).toLinearMap : E →ₗ[𝕜] E) := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [partialTraceRight_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply,
    TensorProduct.inner_tmul, map_smul, restrictRight_tmul]
  simp_rw [mul_smul, smul_smul, ← Finset.sum_smul, ← Finset.mul_sum]
  rw [b.sum_inner_mul_inner b₂ b₁]
  ring_nf

/-- **Spectral form of the reduced density matrix from Schmidt decomposition** (abstract). No
orthogonality is required of `e`. -/
theorem partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt (b : OrthonormalBasis ι₂ 𝕜 F)
    {n : ℕ} {Ψ : E ⊗[𝕜] F}
    (σs : Fin n → ℝ) (e : Fin n → E) (f : Fin n → F)
    (hf : Orthonormal 𝕜 f)
    (hΨ : Ψ = ∑ i, (σs i : 𝕜) • (e i ⊗ₜ[𝕜] f i)) :
    partialTraceRight b ((InnerProductSpace.rankOne 𝕜 Ψ Ψ).toLinearMap) =
      ∑ i, ((σs i : 𝕜) ^ 2) •
        ((InnerProductSpace.rankOne 𝕜 (e i) (e i)).toLinearMap : E →ₗ[𝕜] E) := by
  rw [hΨ, InnerProductSpace.rankOne_sum_smul_sum_smul]
  simp_rw [ContinuousLinearMap.coe_sum, ContinuousLinearMap.coe_smul, RCLike.conj_ofReal,
    ← partialTraceRightLM_apply b, map_sum, map_smul, partialTraceRightLM_apply,
    partialTraceRight_rankOne_tmul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [orthonormal_iff_ite.mp hf, smul_ite, smul_zero, ite_smul, zero_smul, one_smul]
  rw [Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _), sq]

/-- **Delta-orthogonality**: `restrictRight b k ∘ embedRight b k' = if k = k' then id else 0`. -/
theorem restrictRight_comp_embedRight [DecidableEq ι₂]
    (b : OrthonormalBasis ι₂ 𝕜 F) (k k' : ι₂) :
    (restrictRight b k : E ⊗[𝕜] F →ₗ[𝕜] E) ∘ₗ embedRight b k' =
      if k = k' then LinearMap.id else 0 := by
  ext x
  simp only [LinearMap.comp_apply, embedRight_apply, restrictRight_tmul, b.inner_eq_ite]
  split_ifs <;> simp

/-- **Resolution of identity** (right slot): `∑ k, embedRight b k ∘ restrictRight b k = id`. -/
theorem sum_embedRight_comp_restrictRight (b : OrthonormalBasis ι₂ 𝕜 F) :
    ∑ k : ι₂, (embedRight b k : E →ₗ[𝕜] E ⊗[𝕜] F) ∘ₗ restrictRight b k = LinearMap.id := by
  refine TensorProduct.ext' fun x y ↦ ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, restrictRight_tmul, embedRight_apply,
    LinearMap.id_apply, TensorProduct.smul_tmul]
  rw [← TensorProduct.tmul_sum]
  congr 1
  simpa [b.repr_apply_apply] using b.sum_repr y

/-- **Right-equivariance of restrict**: `restrictRight b k ∘ tensorMap A id = A ∘ restrictRight b
k`. Stated for a map `A : E →ₗ E'` that may change the left space; the endomorphism case `E' =
E` is the common instance. -/
theorem restrictRight_comp_tensorMap_id {E' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E'] (b : OrthonormalBasis ι₂ 𝕜 F) (A : E →ₗ[𝕜] E') (k : ι₂) :
    (restrictRight b k : E' ⊗[𝕜] F →ₗ[𝕜] E') ∘ₗ TensorProduct.map A LinearMap.id =
      A ∘ₗ (restrictRight b k : E ⊗[𝕜] F →ₗ[𝕜] E) := by
  refine TensorProduct.ext' fun x y ↦ ?_
  simp [restrictRight_tmul, TensorProduct.map_tmul]

/-- **Right-equivariance of embed**: `tensorMap A id ∘ embedRight b k = embedRight b k ∘ A`. -/
theorem tensorMap_id_comp_embedRight (b : OrthonormalBasis ι₂ 𝕜 F)
    (A : E →ₗ[𝕜] E) (k : ι₂) :
    TensorProduct.map A (LinearMap.id : F →ₗ[𝕜] F) ∘ₗ
        (embedRight b k : E →ₗ[𝕜] E ⊗[𝕜] F) =
      embedRight b k ∘ₗ A := by
  ext x
  simp [embedRight_apply, TensorProduct.map_tmul]

/-- **Left-action equivariance** (right partial trace): partial trace commutes with left
`tensorMap _ id` composition. -/
theorem partialTraceRight_tensorMap_id_comp (b : OrthonormalBasis ι₂ 𝕜 F)
    (A : E →ₗ[𝕜] E) (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceRight b (TensorProduct.map A LinearMap.id ∘ₗ T) =
      A ∘ₗ partialTraceRight b T := by
  refine LinearMap.ext fun x ↦ ?_
  rw [partialTraceRight_apply, LinearMap.comp_apply, partialTraceRight_apply, map_sum A]
  exact Finset.sum_congr rfl fun k _ ↦
    LinearMap.congr_fun (restrictRight_comp_tensorMap_id b A k) (T (embedRight b k x))

/-- **Right-action equivariance** (right partial trace): partial trace commutes with right
`tensorMap _ id` composition. -/
theorem partialTraceRight_comp_tensorMap_id (b : OrthonormalBasis ι₂ 𝕜 F)
    (A : E →ₗ[𝕜] E) (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceRight b (T ∘ₗ TensorProduct.map A LinearMap.id) =
      partialTraceRight b T ∘ₗ A := by
  refine LinearMap.ext fun x ↦ ?_
  rw [partialTraceRight_apply, LinearMap.comp_apply, partialTraceRight_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact congrArg _ (congrArg T (LinearMap.congr_fun (tensorMap_id_comp_embedRight b A k) x))

/-- **Embed is norm-preserving** (right): `‖embedRight b k v‖ = ‖v‖`. -/
theorem norm_embedRight (b : OrthonormalBasis ι₂ 𝕜 F) (k : ι₂) (v : E) :
    ‖embedRight b k v‖ = ‖v‖ := by
  have h_bk : ⟪b k, b k⟫_𝕜 = 1 :=
    inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (b k) ▸ by simp [b.orthonormal.norm_eq_one]
  rw [@norm_eq_sqrt_re_inner 𝕜, embedRight_apply, TensorProduct.inner_tmul,
    @norm_eq_sqrt_re_inner 𝕜, h_bk]
  simp

/-- **Embed inner-product delta** (right): the inner product of two `embedRight` images is
`⟪v, v'⟫` on-diagonal and `0` off-diagonal. -/
theorem inner_embedRight_embedRight [DecidableEq ι₂]
    (b : OrthonormalBasis ι₂ 𝕜 F) (k k' : ι₂) (v v' : E) :
    ⟪embedRight b k v, embedRight b k' v'⟫_𝕜 = if k = k' then ⟪v, v'⟫_𝕜 else 0 := by
  rw [embedRight_apply, embedRight_apply, TensorProduct.inner_tmul, b.inner_eq_ite]
  split_ifs <;> simp

/-- **Pythagorean identity for `embedRight` decompositions** (right): the squared norm of a finite
sum `∑ k, embedRight b k (a k)` is the sum of squared norms `∑ k, ‖a k‖²`. -/
theorem norm_sum_embedRight_sq (b : OrthonormalBasis ι₂ 𝕜 F) (a : ι₂ → E) :
    ‖∑ k, embedRight b k (a k)‖ ^ 2 = ∑ k, ‖a k‖ ^ 2 := by
  classical
  rw [← @inner_self_eq_norm_sq 𝕜, sum_inner, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [inner_sum]
  simp_rw [inner_embedRight_embedRight]
  rw [Finset.sum_ite_eq _ _ (fun _ ↦ _), if_pos (Finset.mem_univ k), inner_self_eq_norm_sq]

/-- **Identity-decomposition via right-slot slicing**: every `w : E ⊗ F` decomposes as
`w = ∑ k, embedRight b k (restrictRight b k w)`. -/
theorem sum_embedRight_restrictRight_eq_self (b : OrthonormalBasis ι₂ 𝕜 F)
    (w : E ⊗[𝕜] F) : ∑ k : ι₂, embedRight b k (restrictRight b k w) = w := by
  have := LinearMap.congr_fun (sum_embedRight_comp_restrictRight (𝕜 := 𝕜) (E := E) b) w
  simpa [LinearMap.sum_apply, LinearMap.comp_apply] using this

/-- **Norm-squared decomposition via right-slot Pythagorean**: `‖w‖² = ∑ k, ‖restrictRight b k w‖²`.
-/
theorem norm_sq_eq_sum_norm_restrictRight_sq (b : OrthonormalBasis ι₂ 𝕜 F)
    (w : E ⊗[𝕜] F) : ‖w‖ ^ 2 = ∑ k, ‖restrictRight b k w‖ ^ 2 := by
  conv_lhs => rw [← sum_embedRight_restrictRight_eq_self b w, norm_sum_embedRight_sq]

/-- **`tensorMap A id` decomposes through right-slot embed/restrict**:
`(TensorProduct.map A id) w = ∑ k, embedRight b k (A (restrictRight b k w))`. -/
theorem tensorMap_id_apply (b : OrthonormalBasis ι₂ 𝕜 F)
    (A : E →ₗ[𝕜] E) (w : E ⊗[𝕜] F) :
    (TensorProduct.map A (LinearMap.id : F →ₗ[𝕜] F)) w =
      ∑ k, embedRight b k (A (restrictRight b k w)) := by
  conv_lhs => rw [← sum_embedRight_restrictRight_eq_self b w, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact LinearMap.congr_fun (tensorMap_id_comp_embedRight b A k) (restrictRight b k w)

/-- **Pointwise upper bound**: `‖(TensorProduct.map A id) w‖ ≤ ‖A.toCLM‖ ⋅ ‖w‖`. -/
theorem norm_tensorMap_id_apply_le [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (A : E →ₗ[𝕜] E) (w : E ⊗[𝕜] F) :
    ‖(TensorProduct.map A (LinearMap.id : F →ₗ[𝕜] F)) w‖ ≤
      ‖A.toContinuousLinearMap‖ * ‖w‖ := by
  set b : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F := stdOrthonormalBasis 𝕜 F
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _)
    (by positivity : (0 : ℝ) ≤ ‖A.toContinuousLinearMap‖ * ‖w‖) two_ne_zero,
    tensorMap_id_apply b, norm_sum_embedRight_sq, mul_pow,
    norm_sq_eq_sum_norm_restrictRight_sq b, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ ↦ by
    rw [← mul_pow]; gcongr; exact A.toContinuousLinearMap.le_opNorm _

/-- **Operator-norm bound**: `‖(TensorProduct.map A id).toCLM‖ ≤ ‖A.toCLM‖`. -/
theorem norm_tensorMap_id_le [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (A : E →ₗ[𝕜] E) :
    ‖(TensorProduct.map A (LinearMap.id : F →ₗ[𝕜] F) :
        E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F).toContinuousLinearMap‖ ≤
      ‖A.toContinuousLinearMap‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_tensorMap_id_apply_le A)

/-- **Operator norm of `TensorProduct.map A id` equals operator norm of `A`** (right slot).
"Tensoring with identity on the right factor" is operator-norm preserving when `F` is
nontrivial. -/
theorem norm_tensorMap_id [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [Nontrivial F]
    (A : E →ₗ[𝕜] E) :
    ‖(TensorProduct.map A (LinearMap.id : F →ₗ[𝕜] F) :
        E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F).toContinuousLinearMap‖ =
      ‖A.toContinuousLinearMap‖ := by
  set b_F := stdOrthonormalBasis 𝕜 F
  haveI : Nonempty (Fin (Module.finrank 𝕜 F)) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  set k₀ := Classical.arbitrary (Fin (Module.finrank 𝕜 F))
  set T := TensorProduct.map A (LinearMap.id : F →ₗ[𝕜] F)
  refine le_antisymm (norm_tensorMap_id_le A)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ψ ↦ ?_)
  have h_commute : T (embedRight b_F k₀ ψ) = embedRight b_F k₀ (A ψ) :=
    LinearMap.congr_fun (tensorMap_id_comp_embedRight b_F A k₀) ψ
  calc ‖A.toContinuousLinearMap ψ‖
      = ‖T (embedRight b_F k₀ ψ)‖ := by
        rw [LinearMap.coe_toContinuousLinearMap', h_commute, norm_embedRight]
    _ ≤ ‖T.toContinuousLinearMap‖ * ‖ψ‖ :=
        (T.toContinuousLinearMap.le_opNorm _).trans_eq (by rw [norm_embedRight])

/-- **Trace identity**: the trace of `partialTraceRight b T` equals the trace of `T`. -/
theorem trace_partialTraceRight [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (b : OrthonormalBasis ι₂ 𝕜 F) (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    LinearMap.trace 𝕜 _ (partialTraceRight b T) = LinearMap.trace 𝕜 _ T := by
  rw [partialTraceRight_eq_sum, map_sum]
  simp_rw [← LinearMap.comp_assoc,
    LinearMap.trace_comp_comm' (R := 𝕜) (embedRight b _) _,
    ← LinearMap.comp_assoc]
  rw [← map_sum]
  congr 1
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  simpa using LinearMap.congr_fun (sum_embedRight_comp_restrictRight b) (T x)

/-- **Abstract trace-level partial-trace duality.** For any `V` on the kept factor `E` and any `T :
E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F`, `trace (TensorProduct.map V id ∘ₗ T) = trace (V ∘ₗ partialTraceRight b
T)`, where `b` is an orthonormal basis on the traced-out factor `F`. The defining duality of the
partial trace (`tr((V ⊗ 1) T) = tr(V · Tr_F T)`).
-/
theorem trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (b : OrthonormalBasis ι₂ 𝕜 F) (V : E →ₗ[𝕜] E)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    LinearMap.trace 𝕜 _ (TensorProduct.map V LinearMap.id ∘ₗ T) =
      LinearMap.trace 𝕜 _ (V ∘ₗ partialTraceRight b T) := by
  conv_lhs => rw [← trace_partialTraceRight b, partialTraceRight_tensorMap_id_comp]

/-- **Basis-independence of the right partial trace**. For any two orthonormal bases on the
traced-out factor `F` (possibly with different index types), the partial trace of `T : E ⊗ F →ₗ
E ⊗ F` over the right factor is the same operator on `E`.
-/
theorem partialTraceRight_eq_of_basis [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {ι₂' : Type*} [Fintype ι₂']
    (b : OrthonormalBasis ι₂ 𝕜 F) (b' : OrthonormalBasis ι₂' 𝕜 F)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceRight b T = partialTraceRight b' T := by
  refine sub_eq_zero.mp <| eq_zero_of_trace_adjoint_comp_self_eq_zero _ ?_
  set Δ := partialTraceRight b T - partialTraceRight b' T with hΔ
  rw [hΔ, LinearMap.comp_sub, map_sub, sub_eq_zero,
    (trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight b Δ.adjoint T).symm,
    (trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight b' Δ.adjoint T).symm]

section ConjIsometry

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- **The partial trace is invariant under conjugating the traced factor by a unitary.** For an
isometry `eF : F ≃ₗᵢ[𝕜] G` and orthonormal basis `b` of `F`,

`Tr_G((I ⊗ eF) T (I ⊗ eF)†) = Tr_F T`
-/
theorem partialTraceRight_conjIsometry (b : OrthonormalBasis ι₂ 𝕜 F) (eF : F ≃ₗᵢ[𝕜] G)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceRight (b.map eF) (TensorProduct.map LinearMap.id eF.toLinearMap ∘ₗ T ∘ₗ
        TensorProduct.map LinearMap.id eF.symm.toLinearMap) = partialTraceRight b T := by
  ext x
  rw [partialTraceRight_apply, partialTraceRight_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hmap : (TensorProduct.map LinearMap.id eF.symm.toLinearMap) (x ⊗ₜ[𝕜] (b.map eF) k)
      = x ⊗ₜ[𝕜] b k := by simp [OrthonormalBasis.map_apply]
  have hr : ∀ w : E ⊗[𝕜] F,
      restrictRight (b.map eF) k ((TensorProduct.map LinearMap.id eF.toLinearMap) w)
        = restrictRight b k w := fun w ↦ by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => simp [OrthonormalBasis.map_apply, eF.inner_map_map]
    | add a c ha hc => simp [ha, hc]
  rw [comp_apply, comp_apply, hmap, hr]

/-- Conjugating by the unitary `I_E ⊗ eF` (as `conjStarAlgEquiv`) leaves the `E`-marginal
unchanged, taken over the `eF`-image basis of `G`. -/
theorem partialTraceRight_conjStarAlgEquiv_congrIsometry [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G] (b : OrthonormalBasis ι₂ 𝕜 F)
    (eF : F ≃ₗᵢ[𝕜] G) (τ : (E ⊗[𝕜] F) →L[𝕜] (E ⊗[𝕜] F)) :
    partialTraceRight (b.map eF)
        ((TensorProduct.congrIsometry (.refl 𝕜 E) eF).conjStarAlgEquiv τ).toLinearMap =
      partialTraceRight b τ.toLinearMap := by
  have hcoe : ((TensorProduct.congrIsometry (.refl 𝕜 E) eF).conjStarAlgEquiv τ).toLinearMap =
      TensorProduct.map LinearMap.id eF.toLinearMap ∘ₗ τ.toLinearMap ∘ₗ
        TensorProduct.map LinearMap.id eF.symm.toLinearMap := by
    rw [LinearIsometryEquiv.conjStarAlgEquiv_toLinearMap, LinearEquiv.conj_apply,
      TensorProduct.toLinearEquiv_congrIsometry]
    simp only [TensorProduct.congr_symm, TensorProduct.toLinearMap_congr]; rfl
  rw [hcoe, partialTraceRight_conjIsometry]

end ConjIsometry

variable {ι₁ : Type*} [Fintype ι₁]

/-- The "embed into the left factor at `b k`" map: `y ↦ b k ⊗ₜ y`. -/
noncomputable def embedLeft (b : OrthonormalBasis ι₁ 𝕜 E) (k : ι₁) : F →ₗ[𝕜] E ⊗[𝕜] F :=
  TensorProduct.mk 𝕜 E F (b k)

@[simp]
theorem embedLeft_apply (b : OrthonormalBasis ι₁ 𝕜 E) (k : ι₁) (y : F) :
    embedLeft b k y = b k ⊗ₜ[𝕜] y := rfl

/-- The "restrict at the `b k` slot of the left factor" map:
`x ⊗ₜ y ↦ ⟨b k, x⟩_E • y`, extended linearly. -/
noncomputable def restrictLeft (b : OrthonormalBasis ι₁ 𝕜 E) (k : ι₁) :
    E ⊗[𝕜] F →ₗ[𝕜] F :=
  (TensorProduct.lid 𝕜 F).toLinearMap ∘ₗ
    TensorProduct.map (innerSL 𝕜 (b k)).toLinearMap LinearMap.id

@[simp]
theorem restrictLeft_tmul (b : OrthonormalBasis ι₁ 𝕜 E) (k : ι₁) (x : E) (y : F) :
    restrictLeft b k (x ⊗ₜ[𝕜] y) = ⟪b k, x⟫_𝕜 • y := rfl

/-- The partial trace of `T : E ⊗ F →ₗ E ⊗ F` over the left factor, parametrized by an OB
on `E`. -/
noncomputable def partialTraceLeft (b : OrthonormalBasis ι₁ 𝕜 E)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) : F →ₗ[𝕜] F :=
  ∑ k : ι₁, restrictLeft b k ∘ₗ T ∘ₗ embedLeft b k

theorem partialTraceLeft_eq_sum (b : OrthonormalBasis ι₁ 𝕜 E)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceLeft b T = ∑ k : ι₁, restrictLeft b k ∘ₗ T ∘ₗ embedLeft b k :=
  rfl

theorem partialTraceLeft_apply (b : OrthonormalBasis ι₁ 𝕜 E)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) (y : F) :
    partialTraceLeft b T y = ∑ k : ι₁, restrictLeft b k (T (b k ⊗ₜ[𝕜] y)) := by
  simp [partialTraceLeft_eq_sum, LinearMap.sum_apply, LinearMap.comp_apply]

/-- **Bundled `partialTraceLeft` as a `LinearMap`**: the partial trace over the left factor, viewed
as a linear map `(E ⊗ F →ₗ E ⊗ F) →ₗ (F →ₗ F)`. -/
noncomputable def partialTraceLeftLM (b : OrthonormalBasis ι₁ 𝕜 E) :
    (E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) →ₗ[𝕜] (F →ₗ[𝕜] F) where
  toFun := partialTraceLeft b
  map_add' T₁ T₂ := by
    simp only [partialTraceLeft_eq_sum, LinearMap.add_comp, LinearMap.comp_add,
      Finset.sum_add_distrib]
  map_smul' c T := by
    simp only [partialTraceLeft_eq_sum, RingHom.id_apply, LinearMap.smul_comp,
      LinearMap.comp_smul, Finset.smul_sum]

@[simp]
theorem partialTraceLeftLM_apply (b : OrthonormalBasis ι₁ 𝕜 E)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceLeftLM b T = partialTraceLeft b T := rfl

/-- **Partial-trace-of-rank-one-pure-tensor identity** (left slot, abstract): for any
pure-tensor inputs `a₁ ⊗ b₁` and `a₂ ⊗ b₂` in `E ⊗ F`,
`partialTraceLeft b (rankOne (a₁ ⊗ b₁) (a₂ ⊗ b₂)) = ⟪a₂, a₁⟫ • rankOne b₁ b₂`. -/
theorem partialTraceLeft_rankOne_tmul (b : OrthonormalBasis ι₁ 𝕜 E)
    (a₁ a₂ : E) (b₁ b₂ : F) :
    partialTraceLeft b ((InnerProductSpace.rankOne 𝕜 (a₁ ⊗ₜ[𝕜] b₁ : E ⊗[𝕜] F)
        (a₂ ⊗ₜ[𝕜] b₂)).toLinearMap) =
      ⟪a₂, a₁⟫_𝕜 • ((InnerProductSpace.rankOne 𝕜 b₁ b₂).toLinearMap : F →ₗ[𝕜] F) := by
  refine LinearMap.ext fun y ↦ ?_
  simp only [partialTraceLeft_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply,
    TensorProduct.inner_tmul, map_smul, restrictLeft_tmul]
  simp_rw [mul_smul, smul_smul]
  rw [← Finset.sum_smul]
  congr 2
  rw [← b.sum_inner_mul_inner a₂ a₁, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- **Spectral form of the reduced density matrix from Schmidt decomposition** (abstract, left
slot). When the bipartite state `Ψ : E ⊗ F` has a Schmidt-form decomposition `Ψ = ∑ σᵢ • (eᵢ ⊗
fᵢ)`, the partial trace over the *left* factor is the diagonal operator `∑ σᵢ² • rankOne fᵢ fᵢ`
on `F`. Only orthonormality of `e` *on the support* `{i | σᵢ ≠ 0}` is needed; no orthogonality
is required of `f`. -/
theorem partialTraceLeft_rankOne_eq_sum_rankOne_of_schmidt (b : OrthonormalBasis ι₁ 𝕜 E)
    {n : ℕ} {Ψ : E ⊗[𝕜] F}
    (σs : Fin n → ℝ) (e : Fin n → E) (f : Fin n → F)
    (he : ∀ i j, σs i ≠ 0 → σs j ≠ 0 → ⟪e i, e j⟫_𝕜 = if i = j then 1 else 0)
    (hΨ : Ψ = ∑ i, (σs i : 𝕜) • (e i ⊗ₜ[𝕜] f i)) :
    partialTraceLeft b ((InnerProductSpace.rankOne 𝕜 Ψ Ψ).toLinearMap) =
      ∑ i, ((σs i : 𝕜) ^ 2) •
        ((InnerProductSpace.rankOne 𝕜 (f i) (f i)).toLinearMap : F →ₗ[𝕜] F) := by
  classical
  rw [hΨ, InnerProductSpace.rankOne_sum_smul_sum_smul]
  simp_rw [ContinuousLinearMap.coe_sum, ContinuousLinearMap.coe_smul, RCLike.conj_ofReal,
    ← partialTraceLeftLM_apply b, map_sum, map_smul, partialTraceLeftLM_apply,
    partialTraceLeft_rankOne_tmul]
  refine Finset.sum_congr rfl fun i _ ↦
    (Finset.sum_eq_single i (fun j _ hji ↦ ?_) (by simp)).trans ?_
  · -- Off-diagonal `j ≠ i` term vanishes: either a zero singular value, or `⟪eⱼ, eᵢ⟫ = 0`.
    rcases eq_or_ne (σs i) 0 with hi | hi
    · simp [hi]
    · rcases eq_or_ne (σs j) 0 with hj | hj
      · simp [hj]
      · rw [he j i hj hi, if_neg hji]; simp
  · -- Diagonal term: `(σᵢ * σᵢ) • ⟪eᵢ, eᵢ⟫ • rankOne fᵢ fᵢ = σᵢ² • rankOne fᵢ fᵢ`.
    rcases eq_or_ne (σs i) 0 with hi | hi
    · simp [hi, zero_pow two_ne_zero]
    · rw [he i i hi hi, if_pos rfl, smul_smul, mul_one, ← sq]

/-- The partial trace of `TensorProduct.map A B` over the left
factor equals `(trace A) • B`. -/
theorem partialTraceLeft_tensorMap [FiniteDimensional 𝕜 E]
    (b : OrthonormalBasis ι₁ 𝕜 E) (A : E →ₗ[𝕜] E) (B : F →ₗ[𝕜] F) :
    partialTraceLeft b (TensorProduct.map A B) = (LinearMap.trace 𝕜 _ A) • B := by
  ext y
  simp only [partialTraceLeft_apply, TensorProduct.map_tmul, restrictLeft_tmul,
    LinearMap.smul_apply, ← Finset.sum_smul]
  rw [← LinearMap.trace_eq_sum_inner A b]

/-- **Delta-orthogonality** (left):
`restrictLeft b k ∘ embedLeft b k' = if k = k' then id else 0`. -/
theorem restrictLeft_comp_embedLeft [DecidableEq ι₁]
    (b : OrthonormalBasis ι₁ 𝕜 E) (k k' : ι₁) :
    (restrictLeft b k : E ⊗[𝕜] F →ₗ[𝕜] F) ∘ₗ embedLeft b k' =
      if k = k' then LinearMap.id else 0 := by
  ext y
  simp only [LinearMap.comp_apply, embedLeft_apply, restrictLeft_tmul, b.inner_eq_ite]
  split_ifs <;> simp

/-- **Resolution of identity** (left slot): `∑ k, embedLeft b k ∘ restrictLeft b k = id`. -/
theorem sum_embedLeft_comp_restrictLeft (b : OrthonormalBasis ι₁ 𝕜 E) :
    ∑ k : ι₁, (embedLeft b k : F →ₗ[𝕜] E ⊗[𝕜] F) ∘ₗ restrictLeft b k = LinearMap.id := by
  refine TensorProduct.ext' fun x y ↦ ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, restrictLeft_tmul, embedLeft_apply,
    LinearMap.id_apply]
  simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
  congr 1
  simpa [b.repr_apply_apply] using b.sum_repr x

/-- **Left-equivariance of restrict** (left partial trace):
`restrictLeft b k ∘ tensorMap id B = B ∘ restrictLeft b k`. -/
theorem restrictLeft_comp_tensorMap_id (b : OrthonormalBasis ι₁ 𝕜 E)
    (B : F →ₗ[𝕜] F) (k : ι₁) :
    (restrictLeft b k : E ⊗[𝕜] F →ₗ[𝕜] F) ∘ₗ TensorProduct.map LinearMap.id B =
      B ∘ₗ restrictLeft b k := by
  refine TensorProduct.ext' fun x y ↦ ?_
  simp [restrictLeft_tmul, TensorProduct.map_tmul]

/-- **Left-equivariance of embed** (left partial trace):
`tensorMap id B ∘ embedLeft b k = embedLeft b k ∘ B`. -/
theorem tensorMap_id_comp_embedLeft (b : OrthonormalBasis ι₁ 𝕜 E)
    (B : F →ₗ[𝕜] F) (k : ι₁) :
    TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) B ∘ₗ
        (embedLeft b k : F →ₗ[𝕜] E ⊗[𝕜] F) =
      embedLeft b k ∘ₗ B := by
  ext y
  simp [embedLeft_apply, TensorProduct.map_tmul]

/-- **Right-action equivariance** (left partial trace): partial trace commutes with right
`tensorMap id _` composition. -/
theorem partialTraceLeft_tensorMap_id_comp (b : OrthonormalBasis ι₁ 𝕜 E)
    (B : F →ₗ[𝕜] F) (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceLeft b (TensorProduct.map LinearMap.id B ∘ₗ T) =
      B ∘ₗ partialTraceLeft b T := by
  refine LinearMap.ext fun y ↦ ?_
  rw [partialTraceLeft_apply, LinearMap.comp_apply, partialTraceLeft_apply, map_sum B]
  exact Finset.sum_congr rfl fun k _ ↦
    LinearMap.congr_fun (restrictLeft_comp_tensorMap_id b B k) (T (embedLeft b k y))

/-- **Left-action equivariance** (left partial trace): partial trace commutes with left
`tensorMap id _` composition. -/
theorem partialTraceLeft_comp_tensorMap_id (b : OrthonormalBasis ι₁ 𝕜 E)
    (B : F →ₗ[𝕜] F) (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceLeft b (T ∘ₗ TensorProduct.map LinearMap.id B) =
      partialTraceLeft b T ∘ₗ B := by
  refine LinearMap.ext fun y ↦ ?_
  rw [partialTraceLeft_apply, LinearMap.comp_apply, partialTraceLeft_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact congrArg _ (congrArg T (LinearMap.congr_fun (tensorMap_id_comp_embedLeft b B k) y))

/-- **Embed is norm-preserving** (left): `‖embedLeft b k v‖ = ‖v‖`. -/
theorem norm_embedLeft (b : OrthonormalBasis ι₁ 𝕜 E) (k : ι₁) (v : F) :
    ‖embedLeft b k v‖ = ‖v‖ := by
  have h_bk : ⟪b k, b k⟫_𝕜 = 1 :=
    inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (b k) ▸ by simp [b.orthonormal.norm_eq_one]
  rw [@norm_eq_sqrt_re_inner 𝕜, embedLeft_apply, TensorProduct.inner_tmul,
    @norm_eq_sqrt_re_inner 𝕜, h_bk]
  simp

/-- **Embed inner-product delta** (left): the inner product of two `embedLeft` images is
`⟪v, v'⟫` on-diagonal and `0` off-diagonal. -/
theorem inner_embedLeft_embedLeft [DecidableEq ι₁]
    (b : OrthonormalBasis ι₁ 𝕜 E) (k k' : ι₁) (v v' : F) :
    ⟪embedLeft b k v, embedLeft b k' v'⟫_𝕜 = if k = k' then ⟪v, v'⟫_𝕜 else 0 := by
  rw [embedLeft_apply, embedLeft_apply, TensorProduct.inner_tmul, b.inner_eq_ite]
  split_ifs <;> simp

/-- **Pythagorean identity for `embedLeft` decompositions** (left). -/
theorem norm_sum_embedLeft_sq (b : OrthonormalBasis ι₁ 𝕜 E) (a : ι₁ → F) :
    ‖∑ k, embedLeft b k (a k)‖ ^ 2 = ∑ k, ‖a k‖ ^ 2 := by
  classical
  rw [← @inner_self_eq_norm_sq 𝕜, sum_inner, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [inner_sum]
  simp_rw [inner_embedLeft_embedLeft]
  rw [Finset.sum_ite_eq _ _ (fun _ ↦ _), if_pos (Finset.mem_univ k), inner_self_eq_norm_sq]

/-- **Identity-decomposition via left-slot slicing**: every `w : E ⊗ F` decomposes as
`w = ∑ k, embedLeft b k (restrictLeft b k w)`. -/
theorem sum_embedLeft_restrictLeft_eq_self (b : OrthonormalBasis ι₁ 𝕜 E)
    (w : E ⊗[𝕜] F) : ∑ k : ι₁, embedLeft b k (restrictLeft b k w) = w := by
  have := LinearMap.congr_fun (sum_embedLeft_comp_restrictLeft (𝕜 := 𝕜) (F := F) b) w
  simpa [LinearMap.sum_apply, LinearMap.comp_apply] using this

/-- **Norm-squared decomposition via left-slot Pythagorean**. -/
theorem norm_sq_eq_sum_norm_restrictLeft_sq (b : OrthonormalBasis ι₁ 𝕜 E)
    (w : E ⊗[𝕜] F) : ‖w‖ ^ 2 = ∑ k, ‖restrictLeft b k w‖ ^ 2 := by
  conv_lhs => rw [← sum_embedLeft_restrictLeft_eq_self b w, norm_sum_embedLeft_sq]

/-- **`tensorMap id B` decomposes through left-slot embed/restrict** (left). -/
theorem tensorMap_id_apply_left (b : OrthonormalBasis ι₁ 𝕜 E)
    (B : F →ₗ[𝕜] F) (w : E ⊗[𝕜] F) :
    (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) B) w =
      ∑ k, embedLeft b k (B (restrictLeft b k w)) := by
  conv_lhs => rw [← sum_embedLeft_restrictLeft_eq_self b w, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact LinearMap.congr_fun (tensorMap_id_comp_embedLeft b B k) (restrictLeft b k w)

/-- **Pointwise upper bound** (left): `‖(TensorProduct.map id B) w‖ ≤ ‖B.toCLM‖ ⋅ ‖w‖`. -/
theorem norm_tensorMap_id_left_apply_le [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (B : F →ₗ[𝕜] F) (w : E ⊗[𝕜] F) :
    ‖(TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) B) w‖ ≤
      ‖B.toContinuousLinearMap‖ * ‖w‖ := by
  set b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E := stdOrthonormalBasis 𝕜 E
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _)
    (by positivity : (0 : ℝ) ≤ ‖B.toContinuousLinearMap‖ * ‖w‖) two_ne_zero,
    tensorMap_id_apply_left b, norm_sum_embedLeft_sq, mul_pow,
    norm_sq_eq_sum_norm_restrictLeft_sq b, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ ↦ by
    rw [← mul_pow]; gcongr; exact B.toContinuousLinearMap.le_opNorm _

/-- **Operator-norm bound** (left): `‖(TensorProduct.map id B).toCLM‖ ≤ ‖B.toCLM‖`. -/
theorem norm_tensorMap_id_left_le [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (B : F →ₗ[𝕜] F) :
    ‖(TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) B :
        E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F).toContinuousLinearMap‖ ≤
      ‖B.toContinuousLinearMap‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_tensorMap_id_left_apply_le B)

/-- **Operator norm of `TensorProduct.map id B` equals operator norm of `B`** (left slot,
under `[Nontrivial E]`). -/
theorem norm_tensorMap_id_left [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [Nontrivial E]
    (B : F →ₗ[𝕜] F) :
    ‖(TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) B :
        E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F).toContinuousLinearMap‖ =
      ‖B.toContinuousLinearMap‖ := by
  set b_E := stdOrthonormalBasis 𝕜 E
  haveI : Nonempty (Fin (Module.finrank 𝕜 E)) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  set k₀ := Classical.arbitrary (Fin (Module.finrank 𝕜 E))
  set T := TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) B
  refine le_antisymm (norm_tensorMap_id_left_le B)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ψ ↦ ?_)
  have h_commute : T (embedLeft b_E k₀ ψ) = embedLeft b_E k₀ (B ψ) :=
    LinearMap.congr_fun (tensorMap_id_comp_embedLeft b_E B k₀) ψ
  calc ‖B.toContinuousLinearMap ψ‖
      = ‖T (embedLeft b_E k₀ ψ)‖ := by
        rw [LinearMap.coe_toContinuousLinearMap', h_commute, norm_embedLeft]
    _ ≤ ‖T.toContinuousLinearMap‖ * ‖ψ‖ :=
        (T.toContinuousLinearMap.le_opNorm _).trans_eq (by rw [norm_embedLeft])

/-- **Trace identity** (left): the trace of `partialTraceLeft b T` equals the trace of `T`. -/
theorem trace_partialTraceLeft [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (b : OrthonormalBasis ι₁ 𝕜 E) (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    LinearMap.trace 𝕜 _ (partialTraceLeft b T) = LinearMap.trace 𝕜 _ T := by
  rw [partialTraceLeft_eq_sum, map_sum]
  simp_rw [← LinearMap.comp_assoc,
    LinearMap.trace_comp_comm' (R := 𝕜) (embedLeft b _) _,
    ← LinearMap.comp_assoc]
  rw [← map_sum]
  congr 1
  refine LinearMap.ext fun y ↦ ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  simpa using LinearMap.congr_fun (sum_embedLeft_comp_restrictLeft b) (T y)

/-- **Abstract trace-level partial-trace duality (left).**
`trace (TensorProduct.map id V ∘ₗ T) = trace (V ∘ₗ partialTraceLeft b T)`,
parametric in `b : OrthonormalBasis ι 𝕜 E` on the traced-out left factor. -/
theorem trace_tensorMap_id_comp_eq_trace_comp_partialTraceLeft [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (b : OrthonormalBasis ι₁ 𝕜 E) (V : F →ₗ[𝕜] F)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    LinearMap.trace 𝕜 _ (TensorProduct.map LinearMap.id V ∘ₗ T) =
      LinearMap.trace 𝕜 _ (V ∘ₗ partialTraceLeft b T) := by
  conv_lhs => rw [← trace_partialTraceLeft b, partialTraceLeft_tensorMap_id_comp]

/-- **Basis-independence of the left partial trace**. Any two orthonormal bases on the traced-out
left factor (possibly with different index types) yield the same partial trace. -/
theorem partialTraceLeft_eq_of_basis [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {ι₁' : Type*} [Fintype ι₁']
    (b : OrthonormalBasis ι₁ 𝕜 E) (b' : OrthonormalBasis ι₁' 𝕜 E)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceLeft b T = partialTraceLeft b' T := by
  refine sub_eq_zero.mp <| eq_zero_of_trace_adjoint_comp_self_eq_zero _ ?_
  set Δ := partialTraceLeft b T - partialTraceLeft b' T with hΔ
  rw [hΔ, LinearMap.comp_sub, map_sub, sub_eq_zero,
    (trace_tensorMap_id_comp_eq_trace_comp_partialTraceLeft b Δ.adjoint T).symm,
    (trace_tensorMap_id_comp_eq_trace_comp_partialTraceLeft b' Δ.adjoint T).symm]

section Adjoint

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- **Adjoint of right-embed**: `(embedRight b k).adjoint = restrictRight b k`. -/
theorem adjoint_embedRight (b : OrthonormalBasis ι₂ 𝕜 F) (k : ι₂) :
    LinearMap.adjoint (embedRight b k : E →ₗ[𝕜] E ⊗[𝕜] F) = restrictRight b k := by
  rw [eq_comm, LinearMap.eq_adjoint_iff]
  intro v u
  refine v.induction_on ?_ ?_ ?_
  · simp
  · intro x y
    simp [embedRight_apply, restrictRight_tmul, TensorProduct.inner_tmul, inner_smul_left,
      mul_comm]
  · intro a b ha hb
    simp [inner_add_left, map_add, ha, hb]

/-- **Adjoint of right-restrict**: `(restrictRight b k).adjoint = embedRight b k`. -/
theorem adjoint_restrictRight (b : OrthonormalBasis ι₂ 𝕜 F) (k : ι₂) :
    LinearMap.adjoint (restrictRight b k : E ⊗[𝕜] F →ₗ[𝕜] E) = embedRight b k := by
  rw [← adjoint_embedRight, LinearMap.adjoint_adjoint]

/-- **Adjoint of left-embed**: `(embedLeft b k).adjoint = restrictLeft b k`. -/
theorem adjoint_embedLeft (b : OrthonormalBasis ι₁ 𝕜 E) (k : ι₁) :
    LinearMap.adjoint (embedLeft b k : F →ₗ[𝕜] E ⊗[𝕜] F) = restrictLeft b k := by
  rw [eq_comm, LinearMap.eq_adjoint_iff]
  intro v u
  refine v.induction_on ?_ ?_ ?_
  · simp
  · intro x y
    simp [embedLeft_apply, restrictLeft_tmul, TensorProduct.inner_tmul, inner_smul_left]
  · intro a b ha hb
    simp [inner_add_left, map_add, ha, hb]

/-- **Adjoint of left-restrict**: `(restrictLeft b k).adjoint = embedLeft b k`. -/
theorem adjoint_restrictLeft (b : OrthonormalBasis ι₁ 𝕜 E) (k : ι₁) :
    LinearMap.adjoint (restrictLeft b k : E ⊗[𝕜] F →ₗ[𝕜] F) = embedLeft b k := by
  rw [← adjoint_embedLeft, LinearMap.adjoint_adjoint]

/-- **Self-adjointness transfer** (right): if `T` is self-adjoint, so is `partialTraceRight b T`. -/
theorem partialTraceRight_isSelfAdjoint (b : OrthonormalBasis ι₂ 𝕜 F)
    {T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (partialTraceRight b T) := by
  rw [isSelfAdjoint_iff, LinearMap.star_eq_adjoint, partialTraceRight_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [LinearMap.adjoint_comp, adjoint_restrictRight, adjoint_embedRight]
  rw [← LinearMap.star_eq_adjoint, hT.star_eq, LinearMap.comp_assoc]

/-- **Self-adjointness transfer** (left): if `T` is self-adjoint, so is `partialTraceLeft b T`. -/
theorem partialTraceLeft_isSelfAdjoint (b : OrthonormalBasis ι₁ 𝕜 E)
    {T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (partialTraceLeft b T) := by
  rw [isSelfAdjoint_iff, LinearMap.star_eq_adjoint, partialTraceLeft_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [LinearMap.adjoint_comp, adjoint_restrictLeft, adjoint_embedLeft]
  rw [← LinearMap.star_eq_adjoint, hT.star_eq, LinearMap.comp_assoc]

/-- **Positivity transfer** (right): if `T` is positive, so is `partialTraceRight b T`. -/
theorem partialTraceRight_isPositive (b : OrthonormalBasis ι₂ 𝕜 F)
    {T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F} (hT : T.IsPositive) :
    (partialTraceRight b T).IsPositive := by
  rw [partialTraceRight_eq_sum]
  apply LinearMap.isPositive_sum
  intro k _
  rw [← adjoint_embedRight]
  exact hT.adjoint_conj _

/-- **Positivity transfer** (left): if `T` is positive, so is `partialTraceLeft b T`. -/
theorem partialTraceLeft_isPositive (b : OrthonormalBasis ι₁ 𝕜 E)
    {T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F} (hT : T.IsPositive) :
    (partialTraceLeft b T).IsPositive := by
  rw [partialTraceLeft_eq_sum]
  apply LinearMap.isPositive_sum
  intro k _
  rw [← adjoint_embedLeft]
  exact hT.adjoint_conj _

/-- **Quadratic form of the right partial trace** as a sum of slice quadratic forms:
`⟪x, (Tr_F T) x⟫ = ∑ k, ⟪x ⊗ b k, T (x ⊗ b k)⟫`. The `E`-marginal pairs `x` against the
`b k`-slices of `T`. -/
theorem inner_partialTraceRight_self (b : OrthonormalBasis ι₂ 𝕜 F)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) (x : E) :
    ⟪x, partialTraceRight b T x⟫_𝕜 = ∑ k, ⟪x ⊗ₜ[𝕜] b k, T (x ⊗ₜ[𝕜] b k)⟫_𝕜 := by
  rw [partialTraceRight_apply, inner_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← adjoint_embedRight b k, LinearMap.adjoint_inner_right, embedRight_apply]

/-- **Quadratic form of the left partial trace** as a sum of slice quadratic forms:
`⟪y, (Tr_E T) y⟫ = ∑ k, ⟪b k ⊗ y, T (b k ⊗ y)⟫`. -/
theorem inner_partialTraceLeft_self (b : OrthonormalBasis ι₁ 𝕜 E)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) (y : F) :
    ⟪y, partialTraceLeft b T y⟫_𝕜 = ∑ k, ⟪b k ⊗ₜ[𝕜] y, T (b k ⊗ₜ[𝕜] y)⟫_𝕜 := by
  rw [partialTraceLeft_apply, inner_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← adjoint_embedLeft b k, LinearMap.adjoint_inner_right, embedLeft_apply]

/-- **Marginal-support vanishing** (right): for a positive `T`, if the `E`-marginal quadratic form
vanishes at `x` (`⟪x, (Tr_F T) x⟫ = 0`), then every slice `⟪x ⊗ b k, T (x ⊗ b k)⟫` has zero real
part. -/
theorem IsPositive.re_inner_tmul_eq_zero_of_inner_partialTraceRight_eq_zero
    (b : OrthonormalBasis ι₂ 𝕜 F) {T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F} (hT : T.IsPositive)
    {x : E} (hx : ⟪x, partialTraceRight b T x⟫_𝕜 = 0) (k : ι₂) :
    RCLike.re ⟪x ⊗ₜ[𝕜] b k, T (x ⊗ₜ[𝕜] b k)⟫_𝕜 = 0 := by
  have hsum : ∑ k, RCLike.re ⟪x ⊗ₜ[𝕜] b k, T (x ⊗ₜ[𝕜] b k)⟫_𝕜 = 0 := by
    rw [← map_sum, ← inner_partialTraceRight_self b T x, hx, map_zero]
  exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ hT.re_inner_nonneg_right _).mp hsum k
    (Finset.mem_univ k)

/-- **Marginal-support vanishing** (left): for a positive `T`, if the `F`-marginal quadratic form
vanishes at `y` (`⟪y, (Tr_E T) y⟫ = 0`), then every slice `⟪b k ⊗ y, T (b k ⊗ y)⟫` has zero real
part. -/
theorem IsPositive.re_inner_tmul_eq_zero_of_inner_partialTraceLeft_eq_zero
    (b : OrthonormalBasis ι₁ 𝕜 E) {T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F} (hT : T.IsPositive)
    {y : F} (hy : ⟪y, partialTraceLeft b T y⟫_𝕜 = 0) (k : ι₁) :
    RCLike.re ⟪b k ⊗ₜ[𝕜] y, T (b k ⊗ₜ[𝕜] y)⟫_𝕜 = 0 := by
  have hsum : ∑ k, RCLike.re ⟪b k ⊗ₜ[𝕜] y, T (b k ⊗ₜ[𝕜] y)⟫_𝕜 = 0 := by
    rw [← map_sum, ← inner_partialTraceLeft_self b T y, hy, map_zero]
  exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ hT.re_inner_nonneg_right _).mp hsum k
    (Finset.mem_univ k)

end Adjoint

section Tower

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  {ιE ιF ιG : Type*} [Fintype ιE] [Fintype ιF] [Fintype ιG]

/-- The associator-conjugation `(assoc.symm.conj T)` acts on a pure tensor by re-associating:
`(assoc.symm.conj T) ((x ⊗ y) ⊗ z) = assoc.symm (T (x ⊗ (y ⊗ z)))`. -/
theorem conj_assoc_symm_tmul (T : E ⊗[𝕜] (F ⊗[𝕜] G) →ₗ[𝕜] E ⊗[𝕜] (F ⊗[𝕜] G))
    (x : E) (y : F) (z : G) :
    (TensorProduct.assoc 𝕜 E F G).symm.conj T ((x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] z) =
      (TensorProduct.assoc 𝕜 E F G).symm (T (x ⊗ₜ[𝕜] (y ⊗ₜ[𝕜] z))) := by
  rw [LinearEquiv.conj_apply, LinearEquiv.symm_symm]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_tmul]

/-- `restrictRight` over the composite factor `F ⊗ G` factors as iterated `restrictRight`s after
re-association: pairing out the `bF j ⊗ bG k` slot equals pairing out `bG k` then `bF j`. -/
private theorem restrictRight_restrictRight_assoc_symm (bF : OrthonormalBasis ιF 𝕜 F)
    (bG : OrthonormalBasis ιG 𝕜 G) (j : ιF) (k : ιG) (w : E ⊗[𝕜] (F ⊗[𝕜] G)) :
    restrictRight bF j (restrictRight bG k ((TensorProduct.assoc 𝕜 E F G).symm w)) =
      restrictRight (bF.tensorProduct bG) (j, k) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul u z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul v g =>
          simp only [TensorProduct.assoc_symm_tmul, restrictRight_tmul, map_smul,
            OrthonormalBasis.tensorProduct_apply, TensorProduct.inner_tmul, mul_smul]
          rw [smul_comm]
      | add z₁ z₂ h₁ h₂ => simp [TensorProduct.tmul_add, h₁, h₂]
  | add w₁ w₂ h₁ h₂ => simp [h₁, h₂]

/-- Restricting the left factor `E` and the inner-right factor `G` commute (the `E`- and `G`-slots
are independent), modulo the re-association `(E ⊗ F) ⊗ G ≃ E ⊗ (F ⊗ G)`. -/
private theorem restrictLeft_restrictRight_assoc_symm (bE : OrthonormalBasis ιE 𝕜 E)
    (bG : OrthonormalBasis ιG 𝕜 G) (e : ιE) (k : ιG) (w : E ⊗[𝕜] (F ⊗[𝕜] G)) :
    restrictLeft bE e (restrictRight bG k ((TensorProduct.assoc 𝕜 E F G).symm w)) =
      restrictRight bG k (restrictLeft bE e w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul u z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul v g => simp [smul_smul, mul_comm]
      | add z₁ z₂ h₁ h₂ => simp [TensorProduct.tmul_add, h₁, h₂]
  | add w₁ w₂ h₁ h₂ => simp [h₁, h₂]

/-- `restrictRight` over `G` slides through the left tensor factor under re-association:
`restrictRight bG k (assoc.symm (a ⊗ m)) = a ⊗ restrictRight bG k m`. -/
private theorem restrictRight_assoc_symm_tmul (bG : OrthonormalBasis ιG 𝕜 G) (k : ιG) (a : E)
    (m : F ⊗[𝕜] G) :
    restrictRight bG k ((TensorProduct.assoc 𝕜 E F G).symm (a ⊗ₜ[𝕜] m)) =
      a ⊗ₜ[𝕜] restrictRight bG k m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul v g => simp
  | add m₁ m₂ h₁ h₂ => simp [TensorProduct.tmul_add, h₁, h₂]

/-- **Tower (`E`-marginal).** Tracing out the composite factor `F ⊗ G` (over the product basis
`bF.tensorProduct bG`) equals re-associating, then tracing out `G`, then `F`:
`Tr_{F⊗G} T = Tr_F (Tr_G (assoc.symm.conj T))`. The two ways of reading off the `E`-marginal of a
tripartite state — directly as `Tr_{F⊗G}`, or iteratively as `Tr_F ∘ Tr_G` — agree. -/
theorem partialTraceRight_tensorProduct_basis (bF : OrthonormalBasis ιF 𝕜 F)
    (bG : OrthonormalBasis ιG 𝕜 G) (T : E ⊗[𝕜] (F ⊗[𝕜] G) →ₗ[𝕜] E ⊗[𝕜] (F ⊗[𝕜] G)) :
    partialTraceRight (bF.tensorProduct bG) T =
      partialTraceRight bF (partialTraceRight bG ((TensorProduct.assoc 𝕜 E F G).symm.conj T)) := by
  ext x
  rw [partialTraceRight_apply, Fintype.sum_prod_type, partialTraceRight_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [partialTraceRight_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [OrthonormalBasis.tensorProduct_apply, conj_assoc_symm_tmul]
  exact (restrictRight_restrictRight_assoc_symm bF bG j k _).symm

/-- **Tower (`F`-marginal / commutation).** Tracing out `E` then `G` equals tracing out `G` then
`E` (modulo re-association): `Tr_E (Tr_G (assoc.symm.conj T)) = Tr_G (Tr_E T)`. Both compute the
`F`-marginal `Tr_{EG}` of a tripartite state. -/
theorem partialTraceLeft_partialTraceRight_assoc (bE : OrthonormalBasis ιE 𝕜 E)
    (bG : OrthonormalBasis ιG 𝕜 G) (T : E ⊗[𝕜] (F ⊗[𝕜] G) →ₗ[𝕜] E ⊗[𝕜] (F ⊗[𝕜] G)) :
    partialTraceLeft bE (partialTraceRight bG ((TensorProduct.assoc 𝕜 E F G).symm.conj T)) =
      partialTraceRight bG (partialTraceLeft bE T) := by
  ext y
  simp only [partialTraceLeft_apply, partialTraceRight_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  rw [conj_assoc_symm_tmul]
  exact restrictLeft_restrictRight_assoc_symm bE bG e k _

/-- **Product marginal across the associator.** For a product operator `map A B` on `E ⊗ (F ⊗ G)`,
re-associating and tracing out `G` keeps `A` on `E` and traces `B` over `G`:
`Tr_G (assoc.symm.conj (map A B)) = map A (Tr_G B)`. -/
theorem partialTraceRight_assoc_conj_map (bG : OrthonormalBasis ιG 𝕜 G) (A : E →ₗ[𝕜] E)
    (B : (F ⊗[𝕜] G) →ₗ[𝕜] (F ⊗[𝕜] G)) :
    partialTraceRight bG ((TensorProduct.assoc 𝕜 E F G).symm.conj (TensorProduct.map A B)) =
      TensorProduct.map A (partialTraceRight bG B) := by
  refine TensorProduct.ext' fun u v ↦ ?_
  rw [partialTraceRight_apply, TensorProduct.map_tmul, partialTraceRight_apply,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [conj_assoc_symm_tmul]
  simp only [TensorProduct.map_tmul, restrictRight_assoc_symm_tmul]

/-- The `LinearMap`-level form of the associator-conjugation `assocIsometry.symm`: conjugating a
continuous operator `T` on `E ⊗ (F ⊗ G)` by the re-association isometry and forgetting
continuity equals the plain `LinearEquiv.conj` of `(TensorProduct.assoc 𝕜 E F G).symm` on
`T.toLinearMap`. -/
theorem assocIsometry_symm_conjStarAlgEquiv_toLinearMap [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    (T : (E ⊗[𝕜] (F ⊗[𝕜] G)) →L[𝕜] (E ⊗[𝕜] (F ⊗[𝕜] G))) :
    ((TensorProduct.assocIsometry 𝕜 E F G).symm.conjStarAlgEquiv T).toLinearMap =
      (TensorProduct.assoc 𝕜 E F G).symm.conj T.toLinearMap := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_toLinearMap]
  congr 1

/-- **Tower (`E`-marginal), `conjStarAlgEquiv` form.** Tracing out `G` from the re-associated
operator `assocIsometry.symm.conjStarAlgEquiv T` and then `F` recovers the `E`-marginal
`Tr_{F⊗G} T`. -/
theorem partialTraceRight_partialTraceRight_assocIsometry_symm_conjStarAlgEquiv
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    (bF : OrthonormalBasis ιF 𝕜 F) (bG : OrthonormalBasis ιG 𝕜 G)
    (T : (E ⊗[𝕜] (F ⊗[𝕜] G)) →L[𝕜] (E ⊗[𝕜] (F ⊗[𝕜] G))) :
    partialTraceRight bF (partialTraceRight bG
        ((TensorProduct.assocIsometry 𝕜 E F G).symm.conjStarAlgEquiv T).toLinearMap) =
      partialTraceRight (bF.tensorProduct bG) T.toLinearMap := by
  rw [assocIsometry_symm_conjStarAlgEquiv_toLinearMap, ← partialTraceRight_tensorProduct_basis]

/-- **`E`-marginal consistency for a tripartite reduced state.** If `ρ_EF` is the `G`-trace of the
re-associated `T` (`hρEF`) and `ρ_E` is the `F ⊗ G`-trace of `T` (`hρE`), then `ρ_E` is the
`F`-trace of `ρ_EF`. -/
theorem partialTraceRight_eq_of_partialTraceRight_assocIsometry
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    (bF : OrthonormalBasis ιF 𝕜 F) (bG : OrthonormalBasis ιG 𝕜 G)
    {T : (E ⊗[𝕜] (F ⊗[𝕜] G)) →L[𝕜] (E ⊗[𝕜] (F ⊗[𝕜] G))}
    {ρEF : (E ⊗[𝕜] F) →L[𝕜] (E ⊗[𝕜] F)} {ρE : E →L[𝕜] E}
    (hρEF : partialTraceRight bG
      ((TensorProduct.assocIsometry 𝕜 E F G).symm.conjStarAlgEquiv T).toLinearMap = ρEF.toLinearMap)
    (hρE : partialTraceRight (bF.tensorProduct bG) T.toLinearMap = ρE.toLinearMap) :
    partialTraceRight bF ρEF.toLinearMap = ρE.toLinearMap := by
  rw [← hρEF, partialTraceRight_partialTraceRight_assocIsometry_symm_conjStarAlgEquiv, hρE]

end Tower

end LinearMap
