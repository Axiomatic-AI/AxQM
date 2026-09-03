/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SteaneStandardForm
import AxQM.Concrete.PauliStringCommutation

/-!
# Concrete: explicit recovery operations for the Steane-code syndrome (Nielsen & Chuang, Ex 10.61)

It answers Nielsen & Chuang, **Exercise 10.61** (§10.5.8, p. 474):

## Main results
* `steaneSyndrome` — the `6`-bit syndrome of a Pauli error, the parity vector of its symplectic
  pairing with the six Figure-10.16 generators `steaneStdGen`.
* `steaneSingleError` — the `22` correctable errors `{I} ∪ {Xᵢ, Yᵢ, Zᵢ}` as index strings.
* `steaneRecovery` — the **explicit recovery table** `β ↦ Eⱼ`: the single-qubit error carrying the
  measured syndrome `β` (and the identity — no correction — for the `64 − 22 = 42` syndromes not
  produced by a single-qubit error, which signal a higher-weight, uncorrectable error).
* `steaneRecovery_steaneSyndrome` — **Exercise 10.61**: recovering from the measured syndrome
  returns exactly the error, `steaneRecovery (steaneSyndrome Eⱼ) = Eⱼ`; since `E†ⱼ = Eⱼ`, this
  is the recovery operation `E†ⱼ`.
* `steaneRecovery_pauliMulIndex_singleError` — the recovery **corrects** the error: the product
  `E†ⱼ Eⱼ` is the identity string (`pauliMulIndex (recovery) (error) = 0`), so recovery-after-error
  restores the codeword.
-/

namespace AxQM.Concrete

/-- The **`6`-bit error syndrome** measured by the Figure-10.16 circuit for a Pauli error `E : Fin 7
→ Fin 4` (Nielsen & Chuang §10.5.8). The `a`-th bit is the parity (over `ZMod 2`) of the
symplectic pairing `pauliAnticommCount (steaneStdGen a) E` of `E` with the `a`-th standard-form
generator `gₐ` (eq. (10.112)). The three `X`-type generators (`a = 0,1,2`) contribute the
Hamming syndrome of the error's `Z`-component, the three `Z`-type generators (`a = 3,4,5`) that
of its `X`-component. -/
def steaneSyndrome (E : Fin 7 → Fin 4) : Fin 6 → ZMod 2 :=
  fun a => (pauliAnticommCount (steaneStdGen a) E : ZMod 2)

/-- The **`22` correctable errors** of the Steane code, indexed by `Fin 22` as Pauli-index strings
`Fin 7 → Fin 4` (`I = 0, X = 1, Y = 2, Z = 3`): `E₀ = I`, then the seven `Xᵢ` (`i = 0,…,6`), the
seven `Yᵢ`, and the seven `Zᵢ`. -/
def steaneSingleError : Fin 22 → Fin 7 → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1],
    ![2, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 2],
    ![3, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0, 0], ![0, 0, 0, 3, 0, 0, 0],
    ![0, 0, 0, 0, 3, 0, 0], ![0, 0, 0, 0, 0, 3, 0], ![0, 0, 0, 0, 0, 0, 3]]

/-- The **explicit recovery table** of Exercise 10.61. For the `64 − 22 = 42` syndromes that no
single-qubit error produces — signalling a higher-weight, uncorrectable error — it returns the
identity string (no correction). -/
def steaneRecovery (β : Fin 6 → ZMod 2) : Fin 7 → Fin 4 :=
  match (List.finRange 22).find? (fun j => decide (steaneSyndrome (steaneSingleError j) = β)) with
  | some j => steaneSingleError j
  | none => fun _ => 0

/-- **Nielsen & Chuang, Exercise 10.61.** *The explicit recovery operation for each measurable
syndrome.* Recovering from the syndrome produced by a single-qubit error returns exactly that error,
`steaneRecovery (steaneSyndrome (steaneSingleError j)) = steaneSingleError j`. Because each `Eⱼ`
is a Hermitian involution (`E†ⱼ = Eⱼ`), the recovery to apply is this same Pauli — Nielsen &
Chuang's recovery operation `E†ⱼ`. -/
theorem steaneRecovery_steaneSyndrome (j : Fin 22) :
    steaneRecovery (steaneSyndrome (steaneSingleError j)) = steaneSingleError j := sorry

/-- **The recovery corrects the error**: the product `E†ⱼ Eⱼ` of the recovery operation and the
error is the identity string (`pauliMulIndex (recovery) (error) = 0`), so applying the
syndrome-selected recovery after `Eⱼ` returns the codeword. This composes
`steaneRecovery_steaneSyndrome`
(the recovery equals `Eⱼ`) with the involution `Eⱼ Eⱼ = I` of a single-qubit Pauli. -/
theorem steaneRecovery_pauliMulIndex_singleError (j : Fin 22) :
    pauliMulIndex (steaneRecovery (steaneSyndrome (steaneSingleError j))) (steaneSingleError j)
      = 0 := sorry

end AxQM.Concrete
