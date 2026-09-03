/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Lean
import Batteries.Tactic.Lint
import AxQM.Meta.HoleManifest

/-!
# Library-integrity gates: `#check_axioms` and `#check_hole_integrity`

The two properties CI enforces about the library as an artifact, as opposed to anything about its
mathematics or its architecture.
-/

open Lean Elab Command

namespace AxQM.Meta

/-- The module a declaration was imported from, if any. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

/-- Compiler-generated auxiliary declarations (equation/congruence/match lemmas emitted for a `def`,
e.g. `f.congr`, `f.congr_simp`, `f.eq_1`, `f.eq_def`, `f.match_1`) are NOT authored
physics-layer content — any operator type they name is a mechanical artifact of the underlying
function's signature, not a violation (e.g. `simp`-ing on a `State` generator emits
`<fn>.congr_simp`, whose type mentions the underlying operator). -/
def isAutoGenAux (n : Name) : Bool :=
  match n with
  | .str _ s =>
      s == "congr" || s == "congr_simp" || s == "eq_def" || s == "eq_unfold"
        || s == "sizeOf_spec" || s == "injEq"
        || s.startsWith "eq_" || s.startsWith "match_" || s.startsWith "proof_"
  | _ => false

/-- Is `n` a **newly-declared `axiom`** belonging to this library? True exactly for an
`axiom` constant authored in a `AxQM.*` module — core/`Mathlib` axioms and
compiler-generated auxiliaries are not this library extending the trusted base. Shared by
the `checkAxiomHygiene` linter and the `#check_axioms` scan, so the CI gate and the
interactive command cannot drift apart. -/
def isNewAxiomDecl (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  match ci with
  | .axiomInfo _ =>
      !n.isInternal && !isAutoGenAux n &&
        (match moduleOf env n with
         | some mod => (`AxQM).isPrefixOf mod
         | none => false)
  | _ => false

/-- `#check_axioms` — scan the imported environment for `AxQM` declarations that
are new `axiom`s and fail if there are any. The scriptable twin of the `checkAxiomHygiene`
env-linter: CI runs it over `import AxQM` (`lake env lean`), which gates the
trusted base *alone*, without the other `runLinter` linters' verdicts. -/
elab "#check_axioms" : command => do
  let env ← getEnv
  let offenders : Array Name := env.constants.fold (init := #[]) fun acc n ci ↦
    if isNewAxiomDecl env n ci then acc.push n else acc
  if offenders.isEmpty then
    logInfo m!"AxQM axiom-hygiene check passed: no new `axiom` declared."
  else
    let msgs := offenders.toList.map fun n ↦ m!"  {n} is a new `axiom`"
    throwError m!"AxQM axiom-hygiene check FAILED: {offenders.size} new \
      `axiom`(s) — the trusted base must not be extended:\n{MessageData.joinSep msgs "\n"}"

/-- **Axiom-hygiene linter**: no `AxQM.*` declaration may be a newly-declared `axiom`.
Environment-based, hence cache-independent and blind to how the axiom was written. -/
@[env_linter] meta def checkAxiomHygiene : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "no declaration declares a new axiom"
  errorsFound := "AxQM axiom hygiene: a declaration declares a new axiom"
  test declName := do
    let env ← getEnv
    let some ci := env.find? declName | return none
    if isNewAxiomDecl env declName ci then
      return some m!"is a new `axiom` — AxQM must not extend the trusted base"
    else return none

/-- Does `n`'s dependency closure reach a declared hole? -/
partial def reachesHole (env : Environment) (n : Name) (seen : NameSet) : Bool × NameSet :=
  if seen.contains n then (false, seen)
  else
    let seen := seen.insert n
    if holeSet.contains n then (true, seen)
    else match env.find? n with
      | none => (false, seen)
      | some ci =>
        -- An inductive's own type is just its sort: everything interesting is in the
        -- CONSTRUCTORS, and `collectAxioms` counts those. Walking only type-and-value would make a
        -- constructor-borne `sorry` look unexplained.
        let extra : Array Name := match ci with
          | .inductInfo iv => iv.ctors.toArray
          | .ctorInfo cv => #[cv.induct]
          | _ => #[]
        let deps := ci.type.getUsedConstants ++
          ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[] ++ extra
        deps.foldl (init := (false, seen)) fun (found, sn) d =>
          if found then (found, sn) else reachesHole env d sn

/-- **The hole-integrity gate.**

`sorry` is legitimate in this library in exactly one place: a declared hole. An unexplained
`sorry` is a hole nobody declared, and that is what this exists to catch.

Deliberately NOT enforced: "a hole's statement is `sorry`-free". The gate reports the count so
the number cannot drift unnoticed, rather than failing on a rule the library knowingly departs
from.
-/
elab "#check_hole_integrity" : command => do
  let env ← getEnv
  -- **Pass 1 — who writes `sorryAx` himself, over everything this project wrote.**
  --
  -- Transitive taint always traces back to some declaration whose own type or value contains
  -- `sorryAx` literally, so checking the direct writers catches every undeclared hole at its
  -- source, without recursion. The scan reaches past `AxQM.*` into the fork-`Mathlib` modules
  -- this project has touched: no declared hole lives there now, and the list is what would
  -- catch an undeclared `sorry` appearing in one.
  let ours (n : Name) : Bool :=
    !n.isInternal && (match moduleOf env n with
      | some mod => (`AxQM).isPrefixOf mod || touchedForkModules.contains mod
      | none => false)
  let mut direct : NameSet := {}
  for (n, ci) in env.constants.toList do
    unless ours n do continue
    let inType := ci.type.getUsedConstants.contains ``sorryAx
    let inValue := ((ci.value? (allowOpaque := true)).map
      (·.getUsedConstants.contains ``sorryAx)).getD false
    if inType || inValue then direct := direct.insert n
  let undeclared := direct.toList.filter fun n ↦ !holeSet.contains n
  -- The converse drift: a name in the manifest that no longer carries a `sorry` — proved,
  -- renamed or deleted.
  let vanished := holeManifest.filterMap fun (nm, _) ↦
    let n := nm.toName
    if direct.contains n then none else some n
  -- **Pass 2 — the benign taint, over our own modules, for the count only.**
  let mut holes := 0
  let mut tainted := 0
  for (n, _) in env.constants.toList do
    unless (!n.isInternal && (match moduleOf env n with
              | some mod => (`AxQM).isPrefixOf mod
              | none => false)) do continue
    if holeSet.contains n then
      holes := holes + 1
    else
      let axs ← Lean.collectAxioms n
      if axs.contains ``sorryAx && (reachesHole env n {}).1 then tainted := tainted + 1
  let fmt (hdr : String) (ns : List Name) (why : String) : MessageData :=
    let lines := ns.take 20 |>.map fun n ↦ m!"  {n} — {why}"
    m!"{hdr} ({ns.length}):\n{MessageData.joinSep lines "\n"}"
  if undeclared.isEmpty && vanished.isEmpty then
    logInfo m!"hole integrity passed: {holeManifest.length} declared holes, all present; \
      {holes} of them in `AxQM.*`, tainting {tainted} further declarations there; \
      0 undeclared `sorry` in any module this project wrote."
  else
    let parts := (if undeclared.isEmpty then [] else
        [fmt "undeclared `sorry`" undeclared "carries `sorry` but is not in `holeManifest`"]) ++
      (if vanished.isEmpty then [] else
        [fmt "stale manifest entry" vanished "declared a hole but carries no `sorry`"])
    throwError m!"hole integrity FAILED:\n{MessageData.joinSep parts "\n"}"

end AxQM.Meta
