# Scripts

What building and checking this library needs, and nothing else. Mathlib's developer and
maintainer tooling — PR labelling, deprecation rewriting, downstream dashboards, benchmarking
harnesses — went with the workflows that ran it.

`lake exe lint-style` requires every entry in this directory to be documented here, so if you
add one, add a line for it.

## Build and check

- `mk_all.lean`
  `lake exe mk_all` regenerates the import aggregators. CI runs `mk_all --check` to keep
  "it compiles" from becoming a green lie after files are added or deleted.

- `lint-style.lean`
  `lake exe lint-style` runs the text-based style linters (line length, trailing whitespace,
  copyright headers, docstring shape). CI gates on it.

- `nolints-style.txt`
  Per-file exceptions read by `lint-style`.

- `print-style-errors.sh`
  A grep wrapper that `Mathlib/Tactic/Linter/TextBased.lean` shells out to for the regex-based
  style checks. Not optional: `lake exe lint-style` fails with
  `could not execute external process` without it.
