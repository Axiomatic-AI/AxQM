/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrix

/-!
# Concrete: the `n`-qubit Pauli group and its faithful check-row representation
-/

open Matrix Complex

open scoped BigOperators

namespace AxQM.Concrete

/-- The **fourth-root-of-unity phase** `iˢ` for `s : ZMod 4`, defined as `Complex.I ^ s.val`. Since
`I⁴ = 1`, this descends from `ℤ`/`ℕ` to `ZMod 4` and is a homomorphism `(ZMod 4, +) → (ℂ, ·)`,
taking the four values `1, i, -1, -i`. It supplies the `±1, ±i` overall factor of a Pauli-group
element. -/
noncomputable def zmod4Pow (s : ZMod 4) : ℂ := Complex.I ^ s.val

@[simp] theorem zmod4Pow_zero : zmod4Pow 0 = 1 := by rw [zmod4Pow]; norm_num

@[simp] theorem zmod4Pow_one : zmod4Pow 1 = Complex.I := by
  rw [zmod4Pow, show (1 : ZMod 4).val = 1 from rfl, pow_one]

@[simp] theorem zmod4Pow_three : zmod4Pow 3 = -Complex.I := by
  rw [zmod4Pow, show (3 : ZMod 4).val = 3 from rfl]; norm_num [pow_succ, Complex.I_mul_I]

/-- `iˢ ≠ 0`. -/
theorem zmod4Pow_ne_zero (s : ZMod 4) : zmod4Pow s ≠ 0 := by
  rw [zmod4Pow]; exact pow_ne_zero _ Complex.I_ne_zero

/-- **The phase is a homomorphism** `(ZMod 4, +) → (ℂ, ·)`: `i^(x+y) = iˣ · iʸ`. -/
theorem zmod4Pow_add (x y : ZMod 4) : zmod4Pow (x + y) = zmod4Pow x * zmod4Pow y := by
  have hI4 : ∀ a : ℕ, Complex.I ^ (a % 4) = Complex.I ^ a := by
    intro a
    conv_rhs => rw [← Nat.div_add_mod a 4, pow_add, pow_mul]
    norm_num [pow_succ, Complex.I_mul_I]
  rw [zmod4Pow, zmod4Pow, zmod4Pow, ZMod.val_add, hI4, pow_add]

/-- The phase `iˢ` is **injective** in `s`: the four values `1, i, -1, -i` are distinct. -/
theorem zmod4Pow_injective : Function.Injective zmod4Pow := by
  intro x y h
  simp only [zmod4Pow] at h
  fin_cases x <;> fin_cases y <;> revert h <;>
    simp only [ZMod.val] <;> norm_num [Complex.ext_iff, pow_succ, Complex.I_mul_I]

/-- The phase carries finite sums to finite products: `i^(∑ᵢ fᵢ) = ∏ᵢ i^(fᵢ)`. -/
theorem zmod4Pow_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 4) :
    zmod4Pow (∑ i ∈ s, f i) = ∏ i ∈ s, zmod4Pow (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zmod4Pow_add, ih]

/-- The **single-qubit product-phase exponent** `singlePhasePow a b : ZMod 4`, the power `s` with
`iˢ = ζ(a, b)` (`pauliMulPhase`) in the single-qubit product `σ_a σ_b = ζ(a,b) σ_{a⊙b}`. -/
def singlePhasePow : Fin 4 → Fin 4 → ZMod 4 :=
  ![![0, 0, 0, 0], ![0, 0, 1, 3], ![0, 3, 0, 1], ![0, 1, 3, 0]]

/-- `singlePhasePow` is the `i`-exponent of the single-qubit product phase: `i^(singlePhasePow a b)
= pauliMulPhase a b`. -/
theorem zmod4Pow_singlePhasePow (a b : Fin 4) :
    zmod4Pow (singlePhasePow a b) = pauliMulPhase a b := by
  fin_cases a <;> fin_cases b <;> simp [singlePhasePow, pauliMulPhase]

/-- The **`n`-qubit product-phase exponent** `phasePow a b : ZMod 4`, the power `s` with `iˢ =
∏ₖ ζ(aₖ, bₖ)` the total phase in the Pauli-string product law. It is the sum of the per-qubit
exponents `∑ₖ singlePhasePow (aₖ) (bₖ)`. -/
def phasePow {n : ℕ} (a b : Fin n → Fin 4) : ZMod 4 := ∑ k, singlePhasePow (a k) (b k)

/-- `i^(phasePow a b) = ∏ₖ pauliMulPhase (aₖ) (bₖ)`: the phase exponent exponentiates to the total
scalar in the Pauli-string product law. -/
theorem zmod4Pow_phasePow {n : ℕ} (a b : Fin n → Fin 4) :
    zmod4Pow (phasePow a b) = ∏ k, pauliMulPhase (a k) (b k) := by
  rw [phasePow, zmod4Pow_sum]
  exact Finset.prod_congr rfl fun k _ => zmod4Pow_singlePhasePow (a k) (b k)

/-- The **`n`-qubit Pauli group** `Gₙ` (Nielsen & Chuang §10.5), modelled abstractly by its data: a
fourth-root-of-unity phase `phase : ZMod 4` (the `iˢ` factor) and a Pauli-string index `idx :
Fin n → Fin 4`. -/
@[ext]
structure PauliGroup (n : ℕ) where
  /-- The fourth-root-of-unity phase power `s` (the overall factor `iˢ`). -/
  phase : ZMod 4
  /-- The Pauli-string index `a : Fin n → Fin 4` (one of `I, X, Y, Z` per qubit). -/
  idx : Fin n → Fin 4

namespace PauliGroup

variable {n : ℕ}

/-- Group multiplication `(s, a) · (t, b) = (s + t + phasePow a b, a ⊙ b)`: indices multiply
componentwise (`pauliMulIndex`) and the phases add, with the extra `phasePow a b` from the
Pauli-string product phase. -/
instance : Mul (PauliGroup n) :=
  ⟨fun p q => ⟨p.phase + q.phase + phasePow p.idx q.idx, pauliMulIndex p.idx q.idx⟩⟩

/-- The identity `(0, 0)`: phase `i⁰ = 1` and the all-identity index (`P₀ = I`). -/
instance : One (PauliGroup n) := ⟨⟨0, 0⟩⟩

/-- Inversion `(s, a)⁻¹ = (-s, a)`: a Pauli string is an involution, so only the phase inverts. -/
instance : Inv (PauliGroup n) := ⟨fun p => ⟨-p.phase, p.idx⟩⟩

@[simp] theorem mul_phase (p q : PauliGroup n) :
    (p * q).phase = p.phase + q.phase + phasePow p.idx q.idx := rfl

@[simp] theorem mul_idx (p q : PauliGroup n) : (p * q).idx = pauliMulIndex p.idx q.idx := rfl

@[simp] theorem one_phase : (1 : PauliGroup n).phase = 0 := rfl

@[simp] theorem one_idx : (1 : PauliGroup n).idx = 0 := rfl

@[simp] theorem inv_phase (p : PauliGroup n) : p⁻¹.phase = -p.phase := rfl

@[simp] theorem inv_idx (p : PauliGroup n) : p⁻¹.idx = p.idx := rfl

/-- The **faithful matrix representation** of a Pauli-group element: `(s, a) ↦ iˢ • P_a`, the
operator `iˢ · pauliString a`. -/
noncomputable def toMat (p : PauliGroup n) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  zmod4Pow p.phase • pauliString p.idx

/-- `toMat` is **multiplicative**: `toMat (p q) = toMat p · toMat q`. -/
theorem toMat_mul (p q : PauliGroup n) : toMat (p * q) = toMat p * toMat q := by
  simp only [toMat, mul_phase, mul_idx]
  rw [smul_mul_smul_comm, pauliString_mul_eq_smul, smul_smul, zmod4Pow_add, zmod4Pow_add,
    zmod4Pow_phasePow]

/-- `toMat` sends the identity to `1`: `i⁰ • P₀ = 1 • I = I`. -/
theorem toMat_one : toMat (1 : PauliGroup n) = 1 := by
  simp only [toMat, one_phase, one_idx, zmod4Pow_zero, one_smul, pauliString_eq_one_iff]

/-- **Faithfulness**: the representation `toMat` is injective — distinct abstract Pauli-group
elements give distinct operators. -/
theorem toMat_injective : Function.Injective (toMat (n := n)) := by
  rintro ⟨s, a⟩ ⟨t, b⟩ h
  simp only [toMat] at h
  have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  have key : ∀ m, zmod4Pow s * (if m = a then (2 : ℂ) ^ n else 0)
      = zmod4Pow t * (if m = b then (2 : ℂ) ^ n else 0) := by
    intro m
    have hh := congrArg (fun M => (pauliString m * M).trace) h
    simpa only [Matrix.mul_smul, Matrix.trace_smul, pauliString_trace_mul, smul_eq_mul] using hh
  have hab : a = b := by
    by_contra hab
    have ea := key a
    rw [if_pos rfl, if_neg hab, mul_zero] at ea
    exact zmod4Pow_ne_zero s ((mul_eq_zero.mp ea).resolve_right h2)
  subst hab
  have ea := key a
  rw [if_pos rfl] at ea
  have hst : s = t := zmod4Pow_injective (mul_right_cancel₀ h2 ea)
  subst hst; rfl

/-- The **`n`-qubit Pauli group** structure on `PauliGroup n`. -/
instance : Group (PauliGroup n) where
  mul_assoc a b c :=
    toMat_injective (by rw [toMat_mul, toMat_mul, toMat_mul, toMat_mul, mul_assoc])
  one_mul a := toMat_injective (by rw [toMat_mul, toMat_one, one_mul])
  mul_one a := toMat_injective (by rw [toMat_mul, toMat_one, mul_one])
  inv_mul_cancel a := toMat_injective (by
    rw [toMat_mul, toMat_one]
    simp only [toMat, inv_phase, inv_idx]
    rw [smul_mul_smul_comm, pauliString_mul_self, ← zmod4Pow_add, neg_add_cancel, zmod4Pow_zero,
      one_smul])

/-- `PauliGroup n` as the plain product type `ZMod 4 × (Fin n → Fin 4)`. -/
def equivProd (n : ℕ) : PauliGroup n ≃ ZMod 4 × (Fin n → Fin 4) where
  toFun p := (p.phase, p.idx)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (PauliGroup n) := Fintype.ofEquiv _ (equivProd n).symm

/-- The **check row of a Pauli-group element**, the check row of its index (the overall phase `iˢ`
is discarded, as the check matrix records no phase information): `checkRowHom (s, a) = checkRow a`.
Valued in the symplectic space `𝔽₂^{2n} = (Fin n → ZMod 2) × (Fin n → ZMod 2)`. -/
def checkRowHom (p : PauliGroup n) : (Fin n → ZMod 2) × (Fin n → ZMod 2) := checkRow p.idx

/-- The Pauli-group element **`-I`**, i.e. `(2, 0)` (`i² · I = -I`). Its non-membership `negOne ∉ S`
in a subgroup `S` is the standing hypothesis `-I ∉ S` of Nielsen & Chuang Proposition 10.3. -/
def negOne (n : ℕ) : PauliGroup n := ⟨2, 0⟩

end PauliGroup

end AxQM.Concrete
