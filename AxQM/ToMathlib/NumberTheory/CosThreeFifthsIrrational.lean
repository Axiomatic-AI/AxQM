/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.NumberTheory.Niven

/-! # An angle with cosine `3/5` is an irrational multiple of `2π`

If `cos θ = 3/5` then `θ / (2π)` is irrational — equivalently, `θ` is not a rational multiple
of `2π`. This is the mathematical content of Nielsen & Chuang's *Quantum Computation and Quantum
Information*, Exercise 4.42 ("Irrationality of `θ`").
-/

@[expose] public section

open Real

/-- **Nielsen & Chuang, Exercise 4.42 (Irrationality of `θ`).** If `cos θ = 3/5` then `θ` is an
irrational multiple of `2π`: the coefficient `θ / (2π)` is an irrational number.
-/
theorem irrational_div_two_pi_of_cos_eq_three_div_five {θ : ℝ}
    (hθ : Real.cos θ = 3 / 5) : Irrational (θ / (2 * π)) := sorry
