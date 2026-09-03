# Scripts

What building and curating this benchmark needs, and nothing else. Mathlib's developer and
maintainer tooling — PR labelling, deprecation rewriting, downstream dashboards, benchmarking
harnesses — went with the workflows that ran it; this repository is a benchmark artifact, not a
mathlib development checkout.

`lake exe lint-style` requires every entry in this directory to be documented here, so if you
add one, add a line for it.

## Build and check

- `mk_all.lean`
  `lake exe mk_all` regenerates `Mathlib.lean` and `AxQM.lean`, the import aggregators.
  Load-bearing: `lean_lib AxQM` has no `globs`, so lake builds only what the aggregator
  transitively imports, and a file missing from it is never compiled. CI runs `mk_all --check`
  to keep "it compiles" from becoming a green lie after files are added or deleted.

- `lint-style.lean`
  `lake exe lint-style` runs the text-based style linters (line length, trailing whitespace,
  copyright headers, docstring shape). CI gates on it.

- `nolints-style.txt`
  Per-file exceptions read by `lint-style`.

- `print-style-errors.sh`
  A grep wrapper that `Mathlib/Tactic/Linter/TextBased.lean` shells out to for the regex-based
  style checks. Not optional: `lake exe lint-style` fails with
  `could not execute external process` without it, which is how it survived this pruning.

## Grading

- `grade`
  What a submission has to satisfy, and the machinery that decides it: the task-type ledger
  generator, the grader, and the entry point that drives both. `lake exe grade` is the whole
  interface for grading a submission; the Python entry point drives the ledger's own
  maintenance. The reason it exists: a task's type is its specification,
  and no ledger recorded the type, so a submission could weaken a statement and still compile,
  still be `sorry`-free, and still add no `axiom`.

