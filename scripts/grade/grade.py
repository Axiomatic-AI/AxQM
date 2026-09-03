#!/usr/bin/env python3
"""Grade a submission, and keep `bench/TASK-FINGERPRINTS.tsv` honest.

A task's type is its specification. Nothing in this repository recorded it: `bench/manifest.json`
carries a task's declaration, kind, module and file, and no ledger carried its statement. So a
submission could weaken a statement — generalise a hypothesis, specialise a conclusion — and pass
every gate there was, because compiling, being `sorry`-free and adding no `axiom` are all things a
weakened statement does too. `bench/TASK-FINGERPRINTS.tsv` closes that, and this drives it.

    python3 scripts/grade/grade.py --emit-names tasks.txt   # the task names, one per line
    python3 scripts/grade/grade.py --regenerate             # rebuild the ledger from the build
    python3 scripts/grade/grade.py --check                  # fail if the ledger has drifted
    python3 scripts/grade/grade.py --grade [name ...]       # grade a built submission
                                                            # naming tasks scopes the CHECK,
                                                            # not just the report
    python3 scripts/grade/grade.py --verify-axioms          # cross-check the sweep on EVERY task

`--regenerate`, `--check` and `--grade` all need a built library, because a type only exists after
elaboration; they shell out to `lake env lean --run`. `--emit-names` reads `bench/manifest.json`
alone and needs nothing.

## What `--check` is for

It keeps this ledger from silently stopping to describe the benchmark. Run it and a statement
cannot change without either the change being deliberate (`--regenerate`, which shows exactly
which statements moved) or this failing.

Note what `--check` does NOT mean: it compares the built library against the ledger, so against
an unmodified checkout it always passes. It earns its keep against a submission, or after any
edit to `AxQM/`, where a failure is the finding rather than a maintenance chore.
"""
import argparse
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEDGER = os.path.join(ROOT, "bench/TASK-FINGERPRINTS.tsv")
MANIFEST = os.path.join(ROOT, "bench/manifest.json")
SCRIPT = "scripts/grade/Grade.lean"


def task_names():
    """The benchmark's task declarations, in the manifest's order."""
    man = json.load(open(MANIFEST))
    return [t["declaration"] for t in man["task_list"]]


def run_lean(script, args):
    """`lake env lean --run <script> <args...>`, streaming stderr through."""
    cmd = ["lake", "env", "lean", "--run", script] + list(args)
    print("+ " + " ".join(cmd), file=sys.stderr)
    return subprocess.run(cmd, cwd=ROOT).returncode


def emit_names(path):
    names = task_names()
    with open(path, "w") as f:
        f.write("\n".join(names) + "\n")
    print(f"wrote {path}: {len(names)} task name(s)")
    return 0


def regenerate(out):
    names = os.path.join(ROOT, "bench/.task-names.txt")
    emit_names(names)
    try:
        rc = run_lean(SCRIPT, ["emit", names, out])
    finally:
        os.remove(names)
    if rc:
        return rc
    with open(out) as f:
        n = sum(1 for line in f if line.strip())
    print(f"wrote {os.path.relpath(out, ROOT)}: {n} fingerprinted task(s)")
    if n != len(task_names()):
        print(f"  WARNING: {len(task_names()) - n} task(s) were not fingerprinted; "
              f"see the stderr list above")
        return 1
    return 0


def check():
    """Diff the committed ledger against one regenerated from the built library.

    On a mismatch the regenerated file is LEFT ON DISK, at `…FINGERPRINTS.tsv.fresh`. That is
    the whole point of keeping it: a type only exists after elaboration, so the freshly elaborated
    types are the one artifact that cannot be reproduced without a build. An intended statement
    change is adopted by taking that file; deleting it would leave the check failing with no way
    to satisfy it.
    """
    if not os.path.exists(LEDGER):
        print(f"no {os.path.relpath(LEDGER, ROOT)} — run --regenerate")
        return 1
    fresh = LEDGER + ".fresh"
    rc = regenerate(fresh)
    if rc and not os.path.exists(fresh):
        return rc
    recorded = open(LEDGER).read()
    now = open(fresh).read()
    if recorded == now:
        os.remove(fresh)
        print("TASK-FINGERPRINTS.tsv up to date: every published fingerprint matches the build")
        return 0
    old = dict(line.split("\t", 1) for line in recorded.splitlines() if "\t" in line)
    new = dict(line.split("\t", 1) for line in now.splitlines() if "\t" in line)
    changed = sorted(k for k in old.keys() & new.keys() if old[k] != new[k])
    gone = sorted(old.keys() - new.keys())
    added = sorted(new.keys() - old.keys())
    print(f"TASK-FINGERPRINTS.tsv is stale: {len(changed)} fingerprint(s) changed, "
          f"{len(gone)} gone, {len(added)} new")
    for k in changed[:10]:
        print(f"  {k}\n    was: {old[k]}\n    now: {new[k]}")
    for k in gone[:10]:
        print(f"  gone: {k}")
    for k in added[:10]:
        print(f"  new:  {k}")
    print(f"the regenerated types are at {os.path.relpath(fresh, ROOT)} and are kept, so an "
          f"intended change can be adopted by taking that file")
    print("if the change is intended, take that file as the new ledger, or rerun --regenerate")
    return 1


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--emit-names", metavar="PATH", help="write the task names and exit")
    ap.add_argument("--regenerate", action="store_true", help="rebuild the fingerprint ledger")
    ap.add_argument("--check", action="store_true",
                    help="fail if the fingerprint ledger has drifted")
    ap.add_argument("--grade", action="store_true", help="grade the built submission")
    ap.add_argument("--verify-axioms", action="store_true",
                    help="cross-check the axiom sweep against collectAxioms on EVERY task")
    ap.add_argument("names", nargs="*", help="with --grade, the tasks to report (default: all)")
    a = ap.parse_args()
    if a.emit_names:
        return emit_names(a.emit_names)
    if a.regenerate:
        return regenerate(LEDGER)
    if a.check:
        return check()
    if a.verify_axioms:
        return run_lean(SCRIPT, ["verify", os.path.relpath(LEDGER, ROOT)])
    if a.grade:
        # The ledger/manifest set comparison is pure file work, so it runs first and for free.
        # `grade` compares every recorded row against the build, which subsumes what `--check`
        # does per row, but it cannot notice a task that exists in the manifest and is MISSING
        # from the ledger — nothing would ask about it. This closes that without a build.
        recorded = {line.split("\t")[0] for line in open(LEDGER) if line.strip()}
        tasks = set(task_names())
        if recorded != tasks:
            missing, extra = sorted(tasks - recorded), sorted(recorded - tasks)
            print(f"ledger and manifest disagree: {len(missing)} task(s) unrecorded, "
                  f"{len(extra)} recorded but not a task")
            for n in missing[:10]:
                print(f"   unrecorded: {n}")
            for n in extra[:10]:
                print(f"   not a task: {n}")
            print("run --regenerate")
            return 1
        return run_lean(SCRIPT, ["grade", os.path.relpath(LEDGER, ROOT)] + a.names)
    ap.print_help()
    return 1


if __name__ == "__main__":
    sys.exit(main())
