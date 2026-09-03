# AxQM — a proof-synthesis benchmark for quantum computing and quantum information

AxQM contains 1019 formal proof-synthesis tasks covering 479 items (exercises, problems, theorems, examples) from *Quantum Computation and Quantum Information* by Nielsen and Chuang, formalized in Lean 4.

## Contents

| | |
|---|---|
| `AxQM/` | the formalized tasks from Nielsen and Chuang, stated in a finite-dimensional quantum physics library |
| `Mathlib/` | the Mathlib fork on which AxQM is built |
| `bench/` | the benchmark metadata: the task index, the per-task proof length estimates, and task identity hashes |
| `scripts/grade/` | the grading script, run as `lake exe grade` |

## Tasks

`bench/manifest.json` is the index of tasks. Each **task** is one Lean statement encoding a part of an **item** from Nielsen and Chuang, with its proof left as `sorry`.

```json
{ "declaration": "Real.entropy_le_add_marginal",
  "kind":        "theorem",
  "module":      "AxQM.ToMathlib.Analysis.SpecialFunctions.JointEntropy",
  "file":        "AxQM/ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean",
  "items":       ["Exercise11_5", "Theorem11_3"],
  "nc_refs":     ["Exercise 11.5", "Theorem 11.3"] }
```

Each textbook item may have multiple tasks (an exercise may ask to show several facts), and some tasks correspond to multiple items (the book states the same fact twice in different places).

We hold private a reference solution library which contains complete proofs of all tasks in the benchmark. This is done to ensure that all tasks are provable, and that the solutions are not leaked.

`bench/task-difficulty.csv` records the proof length estimate for each task, derived from the number of declarations used by the reference solution that are beyond the benchmark library. Tasks are classified into five bands — `very-small`, `small`,
`moderate`, `large`, `very-large`. These may be used as a very rough proxy for difficulty.

The breakdown is as follows:

| band | tasks |
|---|---|
| `very-small` | 158 |
| `small` | 324 |
| `moderate` | 280 |
| `large` | 190 |
| `very-large` | 67 |

## Dependencies between tasks

The pedagogical design of the textbook means that items later in the book often rely on the conclusions of earlier items for their proofs.

`bench/task-dependencies.csv` records the proof dependencies from one task to another, derived from their empirical proof dependencies in the reference solution library.

### Two benchmark regimes

**Independent.** Every task is attempted on its own, with no information about the inter-task dependencies. A valid proof of a task may invoke another task, but that task also has to be proven.

**Dependency-order.** Each task is only attempted once all tasks in its dependency closure have been completed, as defined in `bench/task-dependencies.csv`. A solver may cite these completed prior tasks, but it is not required.

Report which regime was used.

### The three branches

The `main` branch does not contain the benchmark library. To run the benchmark, choose a regime and clone *only* the `independent` branch or the `dependency-order` branch:

```
git clone --single-branch --branch independent https://github.com/Axiomatic-AI/AxQM axqm-independent
git clone --single-branch --branch dependency-order https://github.com/Axiomatic-AI/AxQM axqm-dependency-order
```

## Building

Both the forked Mathlib and the benchmark library have to be built:

```
lake exe cache get
lake build Mathlib AxQM
```

There is **no CI configured**. Anyone building on this repository is responsible for their own.

## Grading

In the repository's root, first run `lake build`, and then run one of:

```
lake exe grade Some.task.name     # grade just this task
lake exe grade                    # every task in the benchmark
```

The grading script checks the following:

1. **The task compiles.**
2. **The proof is `sorry`-free.** The task's dependency closure does not depend on `sorryAx`.
3. **No axiom was added.** The task's dependency closure rests on `propext`, `Classical.choice` and `Quot.sound`, and no other axioms.
4. **The statement is untouched.** The task's type has not been changed. This is enforced by `bench/TASK-FINGERPRINTS.tsv`, which records a Merkle fingerprint of every task's type and the definitions beneath it, computed from the elaborated Lean expression.

## The Mathlib fork

Forked from `leanprover-community/mathlib4` at
[`e560e3ad`](https://github.com/leanprover-community/mathlib4/commit/e560e3ad639d2d8c4c0662784bd40c8b07797781).

One change to mathlib's mathematics: `MultilinearMap` and `PiTensorProduct` are generalized to be semilinear in each argument. This is needed to state the inner product on a tensor power of Hilbert spaces.

Mathlib's own development tooling is not included.

## Licence

Copyright (c) 2026 Axiomatic AI. Released under the Apache License, Version 2.0 — see `LICENSE`.

`AxQM/`, `bench/` and `scripts/grade/` are Axiomatic AI's own work. `Mathlib/`, `Cache/`, `widget/`
and mathlib's scripts are mathlib4, also Apache 2.0, under their own authors' copyright.

`NOTICE` records the fork point, everything this project changed in the forked material, an
additional grant covering database rights in `bench/`, and the standing of the Nielsen and Chuang
material. Under section 4(d) of the licence, a redistribution of this work or a derivative of it
must carry `NOTICE` forward.
