/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AxQM
import Lean

/-!
# Grading a submission

    lake env lean --run scripts/grade/Grade.lean emit  <names.txt> <out.tsv>
    lake env lean --run scripts/grade/Grade.lean grade <ledger.tsv> [task ...]

One script for both jobs, because the fingerprint must be computed identically when publishing and
when grading, and two copies of that code can drift.

## Why this reads terms and never prints them

The first version of this compared **pretty-printed** types as strings. That is not a weak check,
it is the wrong mechanism: `ppExpr` runs in the *submission's* environment, so notation,
`@[app_unexpander]`s and delaborators are all under the solver's control. Anything can be made to
print as anything. A weakened statement could render exactly as the published text.

So nothing here is printed. Fingerprints are folded directly over the elaborated `Expr`, whose
constructors a submission cannot reinterpret, using Lean's own `Expr.hash` and core's `mixHash`
rather than a hash written out here.

A digest is therefore only meaningful against the pinned `lean-toolchain`, since `Expr.hash` may
change between versions. That costs nothing: a toolchain bump is a new benchmark version, and
regenerating the ledger is part of making one.

## Why the fingerprint covers the closure, not just the task's type

Comparing a task's own type is still not enough. A statement's meaning lives in the definitions it
names: leave `AxQM.State` structurally where it is and weaken *its* definition, and the
task's type is unchanged while what it asserts is not.

The fingerprint is therefore a Merkle hash over the task's definitional closure, folded by this
rule:

* out of a **theorem**, follow the **type** only — a proof cannot change what a statement means,
  by proof irrelevance, and the task's own proof is the hole we are asking for;
* out of anything else, follow **type and value**;
* an inductive reaches its constructors, and a constructor its inductive, since the content of an
  inductive lives in the constructors rather than in its own type.

Each constant's hash therefore commits to every definition beneath it. Changing any of them
changes every task that depends on it.

Binder names are dropped, so the comparison is invariant under alpha-renaming. Universe *parameter*
names are kept: renaming those is editing the declaration.

## What the verdicts mean

*Admissible* is checked over every recorded task, not only the ones a solver claims — weakening an
unrelated statement is a way to make your own task easier. One altered fingerprint rejects the
submission whole: there is nothing to grade, because the questions changed.

*Solved* is separate. A task is solved when `collectAxioms` reaches no `sorryAx` and no axiom
outside Lean's own three. `sorry` is the hole as shipped, so an unsolved task is reported as
unsolved, never as a violation. `collectAxioms` walks the whole closure, so a proof leaning on
another task's hole is not solved either.
-/

open Lean

namespace AxQM.Grade

/-- The axioms Lean itself rests on. Anything else in a closure extends the trusted base. -/
def leanAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Which `ConstantInfo` constructor a declaration is. Folded into `selfHash`, so a `def` cannot
become a `theorem`, nor a `theorem` an `axiom`, without the digest moving. -/
def kindTag : ConstantInfo → UInt64
  | .axiomInfo _ => 1 | .defnInfo _ => 2 | .thmInfo _ => 3 | .opaqueInfo _ => 4
  | .quotInfo _ => 5  | .inductInfo _ => 6 | .ctorInfo _ => 7 | .recInfo _ => 8

/-- `DefinitionSafety` has no `Hashable` instance; three cases, mapped by hand. -/
def safetyTag : DefinitionSafety → UInt64
  | .unsafe => 1 | .safe => 2 | .partial => 3

/-- `QuotKind` has no `Hashable` instance; four cases, mapped by hand. -/
def quotTag : QuotKind → UInt64
  | .type => 1 | .ctor => 2 | .lift => 3 | .ind => 4

/-- What a declaration commits to besides its dependencies: its **kind**, its **type**, its
**universe parameters**, and every field of its own `ConstantInfo` that carries meaning.

Hashed with Lean's `Expr.hash` and combined with core's `mixHash`; nothing is hand-rolled.
Three properties of `Expr.hash`, measured against the pinned toolchain rather than assumed:
binder **names** are ignored, so the hash is alpha-invariant; universe **parameter** names are
not; binder **info** is ignored, so `(x : α) → β` and `{x : α} → β` agree — the same
proposition either way, so no weakening hides there.

`mdata` is *not* transparent to `Expr.hash`, and 0.66% of stored types carry one. Elaboration is
deterministic for fixed source and toolchain, so the ledger stays stable; the hash is merely
more sensitive, which errs towards rejecting a submission.

Each of the following was invisible before, and each lets a declaration's identity change while
its digest does not:

* the **kind**. `theorem foo : P` and `axiom foo : P` have the same type, so without this they
  had the same digest. Only the axiom check separated them.
* `levelParams`, **including their order**. `foo.{u,v}` and `foo.{v,u}` share a type `Expr`,
  while `foo.{A,B}` means different things in the two.
* an inductive's `numParams` / `numIndices` / `numNested` / `isRec` / `isReflexive`, and a
  constructor's `cidx` / `numParams` / `numFields`. `inductive Foo (a : α) : β → Prop` and
  `inductive Foo : α → β → Prop` share the type `α → β → Prop` and eliminate differently.
* a recursor's rules, and `unsafe` / `partial` on a definition. -/
def selfHash (ci : ConstantInfo) : UInt64 :=
  let base := mixHash (kindTag ci) (mixHash ci.type.hash (hash ci.levelParams))
  match ci with
  | .thmInfo _ => base    -- a theorem contributes its type; its proof is the hole we ask for
  | .axiomInfo v => mixHash base (hash v.isUnsafe)
  | .defnInfo v =>
      mixHash base (mixHash v.value.hash (mixHash (safetyTag v.safety) (hash v.all)))
  | .opaqueInfo v =>
      mixHash base (mixHash v.value.hash (mixHash (hash v.isUnsafe) (hash v.all)))
  | .quotInfo v => mixHash base (quotTag v.kind)
  | .inductInfo v =>
      mixHash base (mixHash (hash v.numParams) (mixHash (hash v.numIndices)
        (mixHash (hash v.numNested) (mixHash (hash v.isRec) (mixHash (hash v.isUnsafe)
          (mixHash (hash v.isReflexive) (mixHash (hash v.all) (hash v.ctors))))))))
  | .ctorInfo v =>
      mixHash base (mixHash (hash v.induct) (mixHash (hash v.cidx)
        (mixHash (hash v.numParams) (mixHash (hash v.numFields) (hash v.isUnsafe)))))
  | .recInfo v =>
      let rules := v.rules.foldl (fun acc r =>
        mixHash acc (mixHash (hash r.ctor) (mixHash (hash r.nfields) r.rhs.hash))) 0
      mixHash base (mixHash (hash v.numParams) (mixHash (hash v.numIndices)
        (mixHash (hash v.numMotives) (mixHash (hash v.numMinors) (mixHash (hash v.k)
          (mixHash (hash v.isUnsafe) (mixHash (hash v.all) rules)))))))

/-! Domain-separating tags, so that a cycle marker, a constant absent from the environment and a
constant present in it cannot collide with one another by accident. -/

/-- Tag for a constant met again while its own hash is still being computed. -/
def tagRecursive : UInt64 := 0x1
/-- Tag for a constant absent from the environment. -/
def tagAbsent : UInt64 := 0x2
/-- Tag for a constant present in the environment. -/
def tagPresent : UInt64 := 0x3

/-- Structure names reached through a **projection**.

`Expr.getUsedConstants` collects `.const` nodes, and a `.proj S i e` names its structure `S`
outside any `.const` — measured: on `.proj S 0 s` it returns `#[s]` and no `S`. Without this, a
structure a statement reaches only by projecting a field is never folded into the digest, and
weakening that structure goes unseen. -/
partial def projStructs : Expr → Array Name
  | .proj s _ b => #[s] ++ projStructs b
  | .app f a => projStructs f ++ projStructs a
  | .lam _ t b _ => projStructs t ++ projStructs b
  | .forallE _ t b _ => projStructs t ++ projStructs b
  | .letE _ t v b _ => projStructs t ++ projStructs v ++ projStructs b
  | .mdata _ b => projStructs b
  | _ => #[]

/-- Every constant an expression names, the structures behind its projections included. -/
def usedConstants (e : Expr) : Array Name := e.getUsedConstants ++ projStructs e

/-- A constructor stands for its inductive. An inductive and its constructors are one strongly
connected component — the constructors' types mention the inductive, and the inductive's content
*is* its constructors — so they are collapsed into a single node rather than linked in both
directions. Linking both ways made a back edge for essentially every inductive in the environment,
which is not a mutual block and must not be treated as one: with a cycle flag driving a fallback,
almost every task would fall back and the memo would never land. -/
def canon (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo cv) => cv.induct
  | _ => n

/-- Everything a declaration reaches, **including** a theorem's proof, with constructors
canonicalised to their inductive and self-references dropped.

Distinct from `depsFp`, which deliberately stops at a theorem's type: that is right for asking
what a statement *means* and wrong for asking what its proof *rests on*.

An inductive absorbs its constructors' types, which is where an inductive's content lives — its own
type is just a sort. Self-references are dropped because a node's facts cannot depend on itself,
and after canonicalisation a constructor's mention of its own inductive becomes exactly that. -/
def depsAll (env : Environment) (self : Name) (ci : ConstantInfo) : Array Name :=
  let own := ci.type.getUsedConstants
    ++ ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
  let fromCtors := match ci with
    | .inductInfo iv => iv.ctors.toArray.flatMap fun c =>
        match env.find? c with
        | some cci => cci.type.getUsedConstants
        | none => #[]
    | _ => #[]
  (own ++ fromCtors).map (canon env) |>.filter (· != self)

/-- Memo for the axiom sweep: per constant, does its closure reach `sorryAx`, and does it reach an
axiom outside Lean's three. -/
abbrev AxM := StateM (NameMap (Bool × Bool) × NameSet)

/-- The two axiom facts about one constant, plus **whether a dependency cycle was involved**.

`Lean.collectAxioms` answers the facts exactly, but it builds its own state per call, so asking it
1019 times walked the same closure 1019 times — 690s of an 870s grading run, against 7s for a
single shared sweep of the whole environment. This is the same traversal with the memo hoisted out.

Hoisting the memo introduces a hazard that a per-call implementation does not have, and getting it
wrong is a *wrong verdict*, not a slow one. Within a mutual block, a node that meets an active
ancestor cannot yet know that ancestor's axioms; if its own partial answer were memoised, a sibling
carrying `sorryAx` could be missed, and a task depending only on the memoised node would be graded
**solved when it is not**. A first version of this did exactly that.

So the flag is returned alongside the facts. A result reached through a cycle is **never
memoised**, and the caller is told, so it can fall back to `collectAxioms` for that task rather than
trust a partial answer. Cycles are rare enough that the fallback costs little and unsound enough
that guessing is not an option. -/
partial def axiomFacts (env : Environment) (n₀ : Name) : AxM ((Bool × Bool) × Bool) := do
  let n := canon env n₀
  let (memo, active) ← get
  match memo.find? n with
  | some r => return (r, false)
  | none =>
    if active.contains n then
      -- A back edge. Contribute nothing, and tell the caller the answer above is incomplete.
      return ((false, false), true)
    match env.find? n with
    | none => return ((false, false), false)
    | some ci =>
      let own : Bool × Bool := match ci with
        | .axiomInfo _ => (n == ``sorryAx, n != ``sorryAx && !leanAxioms.contains n)
        | _ => (false, false)
      modify fun (m, a) => (m, a.insert n)
      let mut r := own
      let mut cyclic := false
      for d in depsAll env n ci do
        let ((s, b), c) ← axiomFacts env d
        r := (r.1 || s, r.2 || b)
        cyclic := cyclic || c
      modify fun (m, a) => (if cyclic then m else m.insert n r, a.erase n)
      return (r, cyclic)

/-- Memo of closure hashes, plus the set currently being computed (to break recursion). -/
abbrev FpM := StateM (NameMap UInt64 × NameSet)

/-- Everything a declaration's **statement** reaches: `depsAll`'s canonicalisation, but stopping
at a theorem's type rather than following its proof, and including the structures behind any
projection.

The difference from `depsAll` is what a statement *means* versus what a proof *rests on*; the
shared part is what matters here: constructors canonicalise to
their inductive and self-references drop out, so the `inductive ↔ constructor` back edge that
sits under essentially every inductive in the environment is never a cycle at all. -/
def depsFp (env : Environment) (self : Name) (ci : ConstantInfo) : Array Name :=
  let own := usedConstants ci.type
    ++ (match ci with
        | .thmInfo _ => #[]     -- a statement's meaning does not include its proof
        | _ => ((ci.value? (allowOpaque := true)).map usedConstants).getD #[])
  let fromCtors := match ci with
    | .inductInfo iv => iv.ctors.toArray.flatMap fun c =>
        match env.find? c with
        | some cci => usedConstants cci.type
        | none => #[]
    | _ => #[]
  (own ++ fromCtors).map (canon env) |>.filter (· != self)

/-- A node's own content. For an inductive that is its own `selfHash` *and* every constructor's,
since constructors canonicalise into it and are never visited as nodes of their own — an
inductive's content lives in its constructors, so dropping them would leave `numFields`, `cidx`
and the constructor types uncommitted. -/
def nodeSelfHash (env : Environment) (ci : ConstantInfo) : UInt64 :=
  match ci with
  | .inductInfo iv =>
      iv.ctors.foldl (init := selfHash ci) fun acc c =>
        mixHash acc <| match env.find? c with
          | some cci => mixHash (hash c) (selfHash cci)
          | none => mixHash tagAbsent (hash c)
  | _ => selfHash ci

/-- The Merkle hash of a constant: its node's own content, folded with the hashes of everything
that node reaches. Returns the hash and **whether a dependency cycle was involved**, exactly as
`axiomFacts` does, and for the same reason.

On meeting a constant already being computed we can only commit to its name — its content is not
known yet — and a hash built over that placeholder is **never memoised**. Caching one would be
unsound twice over. The cached value does not commit to the ancestor's content, so a later task
reaching this node by another path would not notice that ancestor being weakened. And whether an
entry is placeholder-tainted depends on the order tasks are walked in, so one library could yield
two different digests for the same task — a scoped run disagreeing with a whole-library one, with
the ledger generated in a single pass and therefore looking perfectly self-consistent either way.
`fpcheck` is the mode that tests this. -/
partial def closureHash (env : Environment) (n₀ : Name) : FpM (UInt64 × Bool) := do
  let n := canon env n₀
  match (← get).1.find? n with
  | some h => return (h, false)
  | none =>
    if (← get).2.contains n then
      -- A back edge. Commit to the name only, and tell the caller the answer is incomplete.
      return (mixHash tagRecursive (hash n), true)
    match env.find? n with
    | none =>
      -- Not in the environment: commit to the name, so a vanished constant is not silently
      -- equal to a present one.
      let h := mixHash tagAbsent (hash n)
      modify fun (m, a) => (m.insert n h, a)
      return (h, false)
    | some ci =>
      modify fun (m, a) => (m, a.insert n)
      let mut h := mixHash tagPresent (mixHash (hash n) (nodeSelfHash env ci))
      let mut cyclic := false
      for d in depsFp env n ci do
        let (dh, dc) ← closureHash env d
        h := mixHash h dh
        cyclic := cyclic || dc
      modify fun (m, a) => (if cyclic then m else m.insert n h, a.erase n)
      return (h, cyclic)

/-- The published fingerprint of a task: its kind, type and universe parameters, folded with the
Merkle hash of every constant the type names — the structures behind its projections included.
Its own proof contributes nothing, by proof irrelevance, and is the hole being asked for. -/
def taskFingerprint (env : Environment) (ci : ConstantInfo) : FpM UInt64 := do
  let mut h := mixHash (kindTag ci) (mixHash ci.type.hash (hash ci.levelParams))
  for d in usedConstants ci.type do
    let (dh, _) ← closureHash env d
    h := mixHash h dh
  return h

def hexDigit (d : Nat) : Char :=
  Char.ofNat (if d < 10 then 48 + d else 87 + d)

def hex (u : UInt64) : String :=
  let rec go (fuel : Nat) (v : UInt64) (acc : String) : String :=
    match fuel with
    | 0 => acc
    | fuel + 1 => go fuel (v / 16) (String.singleton (hexDigit (v % 16).toNat) ++ acc)
  go 16 u ""

end AxQM.Grade

open AxQM.Grade

/-- Read one `name <TAB> fingerprint` per line; any further tab-separated columns are advisory and
ignored, so the human-readable column can never affect a verdict. -/
def readLedger (path : String) : IO (List (Name × String)) := do
  let text ← IO.FS.readFile path
  return text.splitOn "\n" |>.filterMap fun line =>
    match line.splitOn "\t" with
    | n :: fp :: _ =>
      if n.trimAscii.isEmpty then none
      else some (n.trimAscii.toString.toName, fp.trimAscii.toString)
    | _ => none

def emit (env : Environment) (names : List Name) (outPath : String) : IO UInt32 := do
  let act : CoreM String := do
    let env ← getEnv
    let mut out : Array String := #[]
    let mut missing : Array Name := #[]
    let mut st : NameMap UInt64 × NameSet := ({}, {})
    for n in names do
      match env.find? n with
      | none => missing := missing.push n
      | some ci =>
        let (h, st') := (taskFingerprint env ci).run st
        st := st'
        out := out.push s!"{n}\t{hex h}"
    if !missing.isEmpty then
      IO.eprintln s!"not in the environment ({missing.size}):"
      for n in missing do IO.eprintln s!"  {n}"
    IO.eprintln s!"fingerprinted {out.size} / {names.length}"
    return String.intercalate "\n" out.toList ++ "\n"
  -- `.toIO'`, not `.run'`: `CoreM.run'` lands in `EIO Exception`, and `IO` is `EIO IO.Error`.
  let text ← act.toIO' { fileName := "Grade", fileMap := default, maxHeartbeats := 0 } { env }
  IO.FS.writeFile outPath text
  return 0

/-- Grade a submission: are the named tasks (or all of them) still the published statement, and
which now carry a real proof?

**Naming tasks restricts what is checked, not merely what is counted.** A task is attempted on
its own, so grading one must not cost the whole benchmark — the scoped run fingerprints and
axiom-sweeps only what was asked for.

Scoping is sound for the verdict it gives. The fingerprint is a Merkle hash over the task's
*definitional* closure, so weakening any definition its statement rests on still moves that
task's own fingerprint; and `collectAxioms` walks the whole *proof* closure, so a proof leaning
on another task's hole, or on an added axiom anywhere in the library, is still caught.

What scoping gives up is the whole-library claim: a submission that also weakens some unrelated
statement, outside the graded task's definitional closure, goes unnoticed. That does not make
the graded task's verdict wrong — it is still proved from its own intact statement — but
"admissible" then means *this task is*, not *the benchmark is*. The report says which. -/
def grade (env : Environment) (recorded : List (Name × String)) (wanted : List Name) :
    IO UInt32 := do
  let isScoped := !wanted.isEmpty
  let unknown := wanted.filter fun n => !(recorded.any fun p => p.1 == n)
  if !unknown.isEmpty then
    IO.eprintln s!"{unknown.length} name(s) are not benchmark tasks — absent from the ledger:"
    for n in unknown do IO.eprintln s!"  {n}"
    IO.eprintln "Task names come from `bench/manifest.json`. `lake exe grade` with no arguments \
      grades every task."
    return 1
  let targets := if isScoped then recorded.filter (fun p => wanted.contains p.1) else recorded
  let act : CoreM UInt32 := do
    let env ← getEnv
    let mut st : NameMap UInt64 × NameSet := ({}, {})
    let mut ax : NameMap (Bool × Bool) × NameSet := ({}, {})
    let mut restated : Array Name := #[]
    let mut missing : Array Name := #[]
    let mut badAxiom : Array Name := #[]
    let mut solved := 0
    let mut unsolved := 0
    let mut crossChecked := 0
    let mut fellBack := 0
    let mut disagreed : Array Name := #[]
    for (n, published) in targets do
      match env.find? n with
      | none => missing := missing.push n
      | some ci =>
        let (h, st') := (taskFingerprint env ci).run st
        st := st'
        if hex h != published then
          restated := restated.push n
        else
          let (((fastSorry, fastAxiom), cyclic), ax') := (axiomFacts env n).run ax
          ax := ax'
          -- A cycle means the fast answer may be incomplete, so defer to the reference
          -- implementation for this task rather than trust it.
          let (hasSorry, hasAxiom) ← if cyclic then do
              fellBack := fellBack + 1
              let axs ← Lean.collectAxioms n
              -- `!isEmpty`, not `.size > 0`: `>` on `Nat` is a `Prop`, so the tuple came out
              -- `Bool × Prop` and would not typecheck.
              pure (axs.contains ``sorryAx,
                    !(axs.filter fun a => !leanAxioms.contains a && a != ``sorryAx).isEmpty)
            else pure (fastSorry, fastAxiom)
          -- The fast sweep is the reference implementation with the memo hoisted out, so it is
          -- cross-checked against `Lean.collectAxioms` on a sample of every run rather than
          -- trusted. Twenty is enough to catch a systematic divergence and costs seconds; a
          -- disagreement fails the run, because a wrong axiom verdict is worse than a slow one.
          if crossChecked < 20 then
            crossChecked := crossChecked + 1
            let axs ← Lean.collectAxioms n
            let refSorry := axs.contains ``sorryAx
            let refAxiom := !(axs.filter fun a => !leanAxioms.contains a && a != ``sorryAx).isEmpty
            if refSorry != hasSorry || refAxiom != hasAxiom then
              disagreed := disagreed.push n
          if hasSorry then
            unsolved := unsolved + 1
          else if hasAxiom then
            badAxiom := badAxiom.push n
          else
            solved := solved + 1
    let scopeLine :=
      if isScoped then s!"tasks graded: {targets.length} of {recorded.length} recorded, as named"
      else s!"tasks graded: {targets.length} (every recorded task)"
    IO.println s!"{scopeLine}  (axiom sweep cross-checked against \
      collectAxioms on {crossChecked}; {fellBack} deferred to it for a dependency cycle)"
    IO.println s!"  solved:   {solved}"
    IO.println s!"  unsolved: {unsolved}"
    if !restated.isEmpty then
      IO.println s!"\nINADMISSIBLE — {restated.size} task(s) no longer match the published \
        fingerprint, in the term or in a definition beneath it:"
      for n in restated do IO.println s!"  {n}"
    if !missing.isEmpty then
      IO.println s!"\nINADMISSIBLE — {missing.size} task declaration(s) are gone:"
      for n in missing do IO.println s!"  {n}"
    if !badAxiom.isEmpty then
      IO.println s!"\nINADMISSIBLE — {badAxiom.size} task(s) rest on an axiom outside Lean's own:"
      for n in badAxiom do IO.println s!"  {n}"
    if !disagreed.isEmpty then
      IO.println s!"\nBUG — the memoised axiom sweep disagrees with `Lean.collectAxioms` on \
        {disagreed.size} of {crossChecked} sampled task(s):"
      for n in disagreed do IO.println s!"  {n}"
      return 1
    if restated.isEmpty && missing.isEmpty && badAxiom.isEmpty then
      if isScoped then
        IO.println s!"\nadmissible: the {targets.length} graded task(s) match their published \
          fingerprint and add no axiom. This is a verdict on those tasks — statements outside \
          their definitional closure were not read."
      else
        IO.println "\nadmissible: every published fingerprint is intact, no axiom added"
      return 0
    return 1
  act.toIO' { fileName := "Grade", fileMap := default, maxHeartbeats := 0 } { env }

/-- Cross-check the memoised sweep against `Lean.collectAxioms` on **every** recorded task.

The routine grading path samples 20, which is evidence rather than proof: if `depsAll` missed an
edge kind that `collectAxioms` follows, a sample would catch it only by luck. This mode closes that
by checking all of them. It costs what the old grading run cost, because it calls the reference
implementation once per task — which is precisely why it is a separate mode and not the default.

It compares only where `grade` **relies** on the fast answer. A cyclic task defers to
`collectAxioms` there, so its fast answer is never consumed, and diffing it would be testing
something no verdict depends on — able to fail on a task `grade` gets right. Those are counted, not
compared. -/
def verify (env : Environment) (recorded : List (Name × String)) : IO UInt32 := do
  let act : CoreM UInt32 := do
    let env ← getEnv
    let mut ax : NameMap (Bool × Bool) × NameSet := ({}, {})
    let mut checked := 0
    let mut deferred := 0
    let mut disagreed : Array (Name × (Bool × Bool) × (Bool × Bool)) := #[]
    for (n, _) in recorded do
      if (env.find? n).isNone then continue
      let (((fastSorry, fastAxiom), cyclic), ax') := (axiomFacts env n).run ax
      ax := ax'
      -- Only compare where `grade` would TRUST the fast answer. A cyclic task never uses it —
      -- `grade` substitutes `collectAxioms` — so diffing it here would test a value nothing
      -- consumes: it could fail on a task `grade` handles correctly, and "agrees on every task"
      -- would be covering answers that are discarded.
      if cyclic then
        deferred := deferred + 1
      else
        let axs ← Lean.collectAxioms n
        let refSorry := axs.contains ``sorryAx
        let refAxiom := !(axs.filter fun a => !leanAxioms.contains a && a != ``sorryAx).isEmpty
        checked := checked + 1
        if refSorry != fastSorry || refAxiom != fastAxiom then
          disagreed := disagreed.push (n, (fastSorry, fastAxiom), (refSorry, refAxiom))
    IO.println s!"compared {checked} task(s) against collectAxioms; {deferred} defer to it for a \
      cycle and are therefore correct by construction"
    if disagreed.isEmpty then
      IO.println "the memoised axiom sweep agrees with collectAxioms wherever grade relies on it"
      return 0
    IO.println s!"\nDISAGREEMENT on {disagreed.size} task(s) — fast (sorry, axiom) vs reference:"
    for (n, f, r) in disagreed do IO.println s!"  {n}: {f} vs {r}"
    return 1
  act.toIO' { fileName := "Grade", fileMap := default, maxHeartbeats := 0 } { env }

/-- Unit assertions on what the fingerprint commits to.

Each of these is a case where a declaration's identity changes, and each was invisible to the
digest before. They are asserted here rather than argued in a comment, and they need no built
library — the `ConstantInfo` values are constructed directly. -/
def selftest : IO UInt32 := do
  let ty : Expr := .sort .zero
  let cval (lps : List Name) : ConstantVal := { name := `T, levelParams := lps, type := ty }
  let defn (lps : List Name) : ConstantInfo := .defnInfo
    { toConstantVal := cval lps, value := .const `V [], hints := .abbrev,
      safety := .safe, all := [`T] }
  let defnSafety (sf : DefinitionSafety) : ConstantInfo := .defnInfo
    { toConstantVal := cval [], value := .const `V [], hints := .abbrev, safety := sf, all := [`T] }
  let thm : ConstantInfo := .thmInfo
    { toConstantVal := cval [], value := .const `V [], all := [`T] }
  let ax : ConstantInfo := .axiomInfo { toConstantVal := cval [], isUnsafe := false }
  let ind (np ni : Nat) (refl : Bool) : ConstantInfo := .inductInfo
    { toConstantVal := cval [], numParams := np, numIndices := ni, all := [`T],
      ctors := [`T.mk], numNested := 0, isRec := false, isUnsafe := false, isReflexive := refl }
  let ctor (cidx nf : Nat) : ConstantInfo := .ctorInfo
    { toConstantVal := cval [], induct := `T, cidx := cidx, numParams := 0,
      numFields := nf, isUnsafe := false }
  let cases : List (String × Bool) :=
    [ ("proj: the structure behind a projection is collected",
        (usedConstants (.proj `S 0 (.const `s []))).contains `S),
      ("levelParams: order matters (foo.{u,v} vs foo.{v,u})",
        selfHash (defn [`u, `v]) != selfHash (defn [`v, `u])),
      ("levelParams: an added parameter matters",
        selfHash (defn []) != selfHash (defn [`u])),
      ("kind: a def is not a theorem of the same type",
        selfHash (defn []) != selfHash thm),
      ("kind: a theorem is not an axiom of the same type",
        selfHash thm != selfHash ax),
      ("definition safety matters (safe vs partial)",
        selfHash (defnSafety .safe) != selfHash (defnSafety .partial)),
      ("inductive: numParams/numIndices matter",
        selfHash (ind 0 1 false) != selfHash (ind 1 0 false)),
      ("inductive: isReflexive matters",
        selfHash (ind 0 0 false) != selfHash (ind 0 0 true)),
      ("constructor: cidx matters",
        selfHash (ctor 0 1) != selfHash (ctor 1 1)),
      ("constructor: numFields matters",
        selfHash (ctor 0 1) != selfHash (ctor 0 2)),
      -- and the control: identical input must agree, or every case above passes vacuously
      ("control: equal inputs agree", selfHash (defn [`u]) == selfHash (defn [`u])) ]
  let failed := cases.filter (!·.2)
  for (name, ok) in cases do
    IO.println s!"  {if ok then "PASS" else "FAIL"}  {name}"
  if failed.isEmpty then
    IO.println s!"\nall {cases.length} assertion(s) hold"
    return 0
  IO.eprintln s!"\n{failed.length} assertion(s) FAILED"
  return 1

/-- Recompute every recorded task's fingerprint from a **cold** state and compare it with the
value the shared, warm state gives when the tasks are walked in sequence.

This is the direct test of the cycle guard in `closureHash`, and close to the only thing that
can see its absence: the ledger is generated in a single pass, so a digest that depends on what
was walked before it is perfectly self-consistent with the ledger and looks healthy. Measured on
Lean's own environment against the code before the guard, 6 of 250 constants hashed differently
warm than cold; with it, 0. -/
def fpcheck (env : Environment) (names : List Name) : IO UInt32 := do
  let mut warm : NameMap UInt64 × NameSet := ({}, {})
  let mut disagreed : Array Name := #[]
  let mut checked := 0
  for n in names do
    if let some ci := env.find? n then
      let (hw, w') := (taskFingerprint env ci).run warm
      warm := w'
      let (hc, _) := (taskFingerprint env ci).run ({}, {})
      checked := checked + 1
      if hw != hc then disagreed := disagreed.push n
  IO.println s!"determinism: {checked} task(s), warm state against cold"
  if disagreed.isEmpty then
    IO.println "  every digest is independent of what was walked before it"
    return 0
  IO.eprintln s!"  {disagreed.size} DIGEST(S) DEPEND ON TRAVERSAL ORDER:"
  for n in disagreed.toList.take 20 do IO.eprintln s!"    {n}"
  return 1

/-- The committed type ledger, relative to the repository root. `lake exe grade` with no
arguments grades against this. -/
def defaultLedger : String := "bench/TASK-FINGERPRINTS.tsv"

def main (args : List String) : IO UInt32 := do
  -- `selftest` asserts properties of the fingerprint's primitives over `ConstantInfo` values it
  -- builds itself, so it needs no environment and no build.
  if args == ["selftest"] then return (← selftest)
  -- Load-bearing for `lake exe grade`. Under `lake env lean --run` the Lean frontend initialises
  -- the module search path before our code runs; a COMPILED executable gets no such favour, and
  -- `importModules` then fails with `unknown module prefix 'AxQM'` against an empty search path.
  -- Idempotent, so the `lake env lean --run` path is unaffected.
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `AxQM }] {} (trustLevel := 1024)
  -- Bare `lake exe grade` grades every task against the committed ledger; `lake exe grade
  -- Some.task` grades only the named ones. The three-argument forms stay for the ledger's own
  -- maintenance.
  let args := match args with
    | [] => ["grade", defaultLedger]
    | a :: _ => if ["emit", "verify", "grade", "fpcheck"].contains a then args
                else "grade" :: defaultLedger :: args
  match args with
  | ["emit", inPath, outPath] =>
    let names := (← IO.FS.readFile inPath).splitOn "\n"
      |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty) |>.map String.toName
    emit env names outPath
  | ["verify", ledgerPath] =>
    let recorded ← readLedger ledgerPath
    if recorded.isEmpty then
      IO.eprintln s!"no fingerprints read from {ledgerPath}"
      return 1
    verify env recorded
  | ["fpcheck"] =>
    fpcheck env ((← readLedger defaultLedger).map (·.1))
  | ["fpcheck", ledgerPath] =>
    fpcheck env ((← readLedger ledgerPath).map (·.1))
  | "grade" :: ledgerPath :: rest =>
    let recorded ← readLedger ledgerPath
    if recorded.isEmpty then
      IO.eprintln s!"no fingerprints read from {ledgerPath}"
      return 1
    grade env recorded (rest.map String.toName)
  | _ =>
    IO.eprintln "usage: lake exe grade                 grade every task"
    IO.eprintln "       lake exe grade <task> ...       grade only these"
    IO.eprintln "       lake exe grade emit   <names.txt> <out.tsv>"
    IO.eprintln "       lake exe grade grade  <ledger.tsv> [task ...]"
    IO.eprintln "       lake exe grade verify <ledger.tsv>"
    IO.eprintln "       lake exe grade fpcheck [ledger.tsv]  digests independent of order?"
    IO.eprintln "       lake exe grade selftest              what the digest commits to"
    return 1
