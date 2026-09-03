/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Tactic

/-!
# Concrete: the adaptive classical query (decision-tree) model

This is shared infrastructure for the classical query lower bounds of Nielsen & Chuang §6.3,
which assert that classical counting takes `Ω(N)` oracle calls. To make the notion of an
algorithm making at most `T` oracle calls precise we use the standard **decision-tree** model of
classical query complexity.
-/

namespace AxQM.Concrete

/-- An **adaptive classical decision tree** querying a Boolean oracle on `Fin N`. This is the
standard model of a deterministic classical algorithm making oracle calls. -/
inductive QueryTree (N : ℕ) : Type where
  | leaf (estimate : ℝ) : QueryTree N
  | node (i : Fin N) (branch : Bool → QueryTree N) : QueryTree N

namespace QueryTree

/-- The real estimate the algorithm outputs when run against the oracle `f`. -/
def eval {N : ℕ} (f : Fin N → Bool) : QueryTree N → ℝ
  | .leaf r => r
  | .node i br => eval f (br (f i))

/-- The worst-case number of oracle calls the algorithm makes: the height of the decision tree. -/
def depth {N : ℕ} : QueryTree N → ℕ
  | .leaf _ => 0
  | .node _ br => max (depth (br false)) (depth (br true)) + 1

end QueryTree

end AxQM.Concrete
