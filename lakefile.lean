import Lake

open Lake DSL

/-!
## Mathlib dependencies on upstream projects
-/

require "leanprover-community" / "batteries" @ git "v4.30.0-rc1"
require "leanprover-community" / "Qq" @ git "v4.30.0-rc1"
require "leanprover-community" / "aesop" @ git "v4.30.0-rc1"
require "leanprover-community" / "proofwidgets" @ git "v0.0.97"
  with NameMap.empty.insert `errorOnBuild
    "ProofWidgets failed to reuse pre-built JS code. \
    Please report this issue on the Lean Zulip."
require "leanprover-community" / "importGraph" @ git "main"
require "leanprover-community" / "LeanSearchClient" @ git "main"
require "leanprover-community" / "plausible" @ git "main"


/-!
## Options for building mathlib
-/

/-- These options are used as `leanOptions`, prefixed by `` `weak``, so that
`lake build` uses them. -/
abbrev mathlibOnlyLinters : Array LeanOption := #[
  ⟨`linter.mathlibStandardSet, true⟩,
  -- Explicitly enable the header linter, since the standard set is defined in `Mathlib.Init`
  -- but we want to run this linter in files imported by `Mathlib.Init`.
  ⟨`linter.style.header, true⟩,
  ⟨`linter.checkInitImports, true⟩,
  ⟨`linter.allScriptsDocumented, true⟩,
  ⟨`linter.pythonStyle, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩,
  -- OFF, so that `lint-style` can cover `AxQM` at all. A benchmark file is named for the
  -- Nielsen & Chuang item it states: `NC/Ch10/Exercise10_1.lean` is "Exercise 10.1", and that
  -- mapping is how a reader gets from a file to the book. This linter wants `Exercise101`,
  -- which would erase the item number.
  --
  -- Measured before disabling it: over `AxQM` this rule was the *entire* backlog — 505 errors
  -- and not one from any other text linter. That count was taken before the declaration-free
  -- item anchors were deleted, so fewer files carry such a name now; the rule stays off because
  -- the naming is deliberate, not because of any particular count.
  --
  -- What the exception buys is therefore the rest of the TEXT linter over 1159 files that no
  -- `lint-style` run had ever read: adaptation notes, trailing whitespace, whitespace before a
  -- semicolon, and the unicode linter. Not the 100-column or file-length rules — those are
  -- elaboration-time linters and already applied, which a planted 143-column line confirmed by
  -- *not* being reported here.
  --
  -- It also switches off the forbidden-filename check, for both libraries. `modulesOSForbidden`
  -- (Windows-reserved names like `CON`/`LPT1`, and characters such as `*`, `?`, `!`) guards on
  -- `linter.modulesUpperCamelCase` rather than on its own `linter.modulesForbiddenWindows`, so
  -- the two cannot be separated — an upstream bug, and not one to fix here, since patching
  -- `Mathlib/` is the diff this project spent PRs #43–#55 removing.
  --
  -- The option is unioned across default targets, so it also stops checking mathlib's own module
  -- names. That loss is vacuous here rather than merely small: this project adds 0 files to
  -- `Mathlib/`, so the check has nothing to guard.
  ⟨`linter.modulesUpperCamelCase, false⟩,
  -- ⟨`linter.nightlyRegressionSet, true⟩,
  -- `latest_import.yml` uses this comment: if you edit it, make sure that the workflow still works
]

/-- These options are passed as `leanOptions` to building mathlib and `AxQM`. -/
abbrev mathlibLeanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
  ] ++ -- options that are used in `lake build`
    mathlibOnlyLinters.map fun s ↦ { s with name := `weak ++ s.name }

package mathlib where
  -- These are additional settings which do not affect the lake hash,
  -- so they can be enabled in CI and disabled locally or vice versa.
  -- Warning: Do not put any options here that actually change the olean files,
  -- or inconsistent behavior may result
  -- weakLeanArgs := #[]

/-!
## Mathlib libraries
-/

@[default_target]
lean_lib Mathlib where
  -- Enforce Mathlib's default linters and style options.
  leanOptions := mathlibLeanOptions

-- NB. When adding further libraries, check if they should be excluded from `getLeanLibs` in
-- `scripts/mk_all.lean`.
lean_lib Cache where
  globs := #[`Cache.+]

/-- `AxQM`: quantum information theory over the primitives (ported from the
fork's `Mathlib`).

A default target, so that a bare `lake build` compiles the benchmark. It is the library a solver
edits, and while `Mathlib` alone was the default a solver could fill a hole, run `lake build`, see
it succeed, and have compiled none of their own work.

Being a default target also widens what `lake exe lint-style` lints, since with no arguments it
takes the default targets' roots. CI therefore names `Mathlib` explicitly — see the rationale on
the "Lint style" step in `.github/workflows/ci.yml`. -/
@[default_target]
lean_lib AxQM where
  leanOptions := mathlibLeanOptions

/-!
## Executables

Only what building and checking the benchmark needs: the olean cache, the import-aggregator
generator, and the text style linter. Mathlib's PR-workflow executables (`autolabel`,
`check_title_labels`, `nightly-testing-checklist`) went with the scripts they ran.
-/

/-- `lake exe cache get` retrieves precompiled `.olean` files from a central server. -/
lean_exe cache where
  root := `Cache.Main

/-- `lake exe mk_all` constructs the files containing all imports for a project. -/
lean_exe mk_all where
  srcDir := "scripts"
  supportInterpreter := true
  -- Executables which import `Lake` must set `-lLake`.
  weakLinkArgs := #["-lLake"]

/-- `lake exe grade` grades a submission against `bench/TASK-FINGERPRINTS.tsv`: a task's
statement still matches the ledger, and whether it now carries a real proof.

`lake exe grade Some.task` grades that task alone — it *checks* only that task, not merely
reports on it, since a submission normally fills one hole and grading it should not cost the
whole benchmark. `lake exe grade` with no arguments grades all 1019, which is the mode that also
asserts no unrelated statement moved.

Run from the repository root, and after `lake build`, since a type exists only once
elaborated. -/
lean_exe grade where
  srcDir := "scripts/grade"
  root := `Grade
  supportInterpreter := true

/-- `lake exe lint-style` runs text-based style linters. -/
lean_exe «lint-style» where
  srcDir := "scripts"
  supportInterpreter := true
  -- Executables which import `Lake` must set `-lLake`.
  weakLinkArgs := #["-lLake"]

/-!
## Other configuration
-/

/--
When a package depending on Mathlib updates its dependencies,
update its toolchain to match Mathlib's and fetch the new cache.
-/
post_update pkg do
  let rootPkg ← getRootPackage
  if rootPkg.baseName = pkg.baseName then
    return -- do not run in Mathlib itself
  if (← IO.getEnv "MATHLIB_NO_CACHE_ON_UPDATE") != some "1" then
    -- Check if Lake version matches toolchain version
    let toolchainFile := rootPkg.dir / "lean-toolchain"
    let toolchainContent ← IO.FS.readFile toolchainFile
    let toolchainVersion := match toolchainContent.trimAscii.copy.splitOn ":" with
      | [_, version] => version
      | _ => toolchainContent.trimAscii.copy  -- fallback to full content if format is unexpected
    -- Lean.versionString does not start with a `v`, while the `lean-toolchain` file is flexible.
    let toolchainVersion := (toolchainVersion.dropPrefix "v").copy
    if Lean.versionString ≠ toolchainVersion then
      IO.println s!"Not running `lake exe cache get` yet, as \
        the `lake` version ({Lean.versionString}) does not match \
        the toolchain version ({toolchainVersion}) in the project.\n\
        You should run `lake exe cache get` manually."
      return
    let exeFile ← runBuild cache.fetch
    -- Run the command in the root package directory,
    -- which is the one that holds the .lake folder and lean-toolchain file.
    let cwd ← IO.Process.getCurrentDir
    let exitCode ← try
      IO.Process.setCurrentDir rootPkg.dir
      env exeFile.toString #["get"]
    finally
      IO.Process.setCurrentDir cwd
    if exitCode ≠ 0 then
      error s!"{pkg.baseName}: failed to fetch cache"
