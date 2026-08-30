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
  -- ⟨`linter.nightlyRegressionSet, true⟩,
  -- `latest_import.yml` uses this comment: if you edit it, make sure that the workflow still works
]

/-- These options are passed as `leanOptions` to building mathlib. -/
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

/-!
## Executables
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
