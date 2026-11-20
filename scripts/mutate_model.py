#!/usr/bin/env python3
"""
Mutation test of the Lean model.

Usage: python3 scripts/mutate_model.py [--only NAME,NAME,...]

Copies the project into a temporary directory, with the build outputs, and for
each named mutant of a definition runs `lake build Dahlias` there. Prints the
declarations that no longer compile. A mutant that builds is a survivor: the
theorems do not depend on what it changes. The script fails if there is one.

The copy uses `cp -c` (copy-on-write on APFS) when it can, so it needs little
disk space on macOS. Elsewhere it copies the dependencies' build outputs too.
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# (name, description, [(file, old, new)]); old must occur exactly once.
MUTANTS = [
    ("unique", "Sign accepts lists in which the signer's R2 appears more than once",
     [("Dahlias/Basic.lean", "  | [j] =>\n    if pm[j]? = some (O.x P, m) then",
       "  | j :: _ =>\n    if pm[j]? = some (O.x P, m) then")]),
    ("message", "Sign does not compare the message at the signer's index",
     [("Dahlias/Basic.lean", "    if pm[j]? = some (O.x P, m) then", "    if (pm[j]?).isSome then")]),
    ("coef", "the nonce coefficient does not cover the signers' R2",
     [("Dahlias/Basic.lean", "(pkm.1, pkm.2, N.2)", "(pkm.1, pkm.2, 0)")]),
    ("twice", "a session can be closed twice",
     [("Dahlias/Security.lean",
       "if h : k < qs ∧ k < st.opened ∧ k ∉ st.closed ∧ τ.2 ≠ 0 ∧ pm.length ≤ N then",
       "if h : k < qs ∧ k < st.opened ∧ True ∧ τ.2 ≠ 0 ∧ pm.length ≤ N then")]),
    ("signed", "a forgery may be for an entry the signer signed",
     [("Dahlias/Security.lean",
       "(∃ m, (C.x (C.mulG (f.τ.sk x)), m) ∈ f.L ∧ (f.L, C.x (C.mulG (f.τ.sk x)), m) ∉ st.signed) ∧",
       "(∃ m, (C.x (C.mulG (f.τ.sk x)), m) ∈ f.L) ∧")]),
    ("count", "hash queries are not counted",
     [("Dahlias/Security.lean", "| .ask (.hash _) f, qh => 0 < qh ∧ ∀ r, HashBound (f r) (qh - 1)",
       "| .ask (.hash _) f, qh => ∀ r, HashBound (f r) qh")]),
    ("omdl", "the AOMDL solver must make two queries fewer than it has challenges",
     [("Dahlias/Security.lean", "out.1 = chalLogs ω.1 out.2.1 ∧ out.2.2 < out.2.1",
       "out.1 = chalLogs ω.1 out.2.1 ∧ out.2.2 + 1 < out.2.1")]),
    ("derived", "the derived nonce of a single-party signature ignores r2",
     [("Dahlias/Security.lean",
       "if der then ν.1 + nonceCoef 0 0 ((singleNcIn (E := E) L).2.2) * ν.2 else ν.1",
       "if der then ν.1 + 0 * (nonceCoef 0 0 ((singleNcIn (E := E) L).2.2) * ν.2) else ν.1")]),
    ("parity", "Sign does not negate the nonce for an R with odd y",
     [("Dahlias/Basic.lean", "(if O.hasEvenY R then k else -k) + c * O.evenScalar sk",
       "k + c * O.evenScalar sk")]),
    ("lift", "Verify does not check that the public keys lift",
     [("Dahlias/Basic.lean", "!pm.isEmpty && pm.all (fun pkm => (O.liftX pkm.1).isSome) &&",
       "!pm.isEmpty &&"),
      ("Dahlias/LazyGame.lean", "!pm.isEmpty && pm.all (fun pkm => (O.liftX pkm.1).isSome) &&",
       "!pm.isEmpty &&")]),
]

DECL = re.compile(r"^(?:noncomputable |private |protected )*(?:def|theorem|lemma|abbrev|instance)\s+(\S+)")


def copy_project(dst):
    """The project with its build outputs, copy-on-write if the file system can."""
    for flags in (["-c", "-R"], ["-R"]):
        if subprocess.run(["cp", *flags, str(ROOT) + "/.", str(dst)],
                          capture_output=True).returncode == 0:
            return
        shutil.rmtree(dst, ignore_errors=True)
        dst.mkdir()
    sys.exit("could not copy the project")


def failures(tree, out):
    """The declarations around the errors of a build log, in the log's order.
    Lake does not build what depends on a module that failed, so these are the
    declarations nearest to the mutated definition."""
    found = []
    for m in re.finditer(r"^error: (Dahlias/\S+\.lean):(\d+):\d+: ", out, re.M):
        path, line = m.group(1), int(m.group(2))
        lines = (tree / path).read_text().split("\n")
        where = f"{path}:{line}"
        for i in range(min(line, len(lines)) - 1, -1, -1):
            d = DECL.match(lines[i])
            if d:
                where = f"{d.group(1)} ({path})"
                break
        if where not in found:
            found.append(where)
    return found


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", help="comma-separated mutant names")
    args = ap.parse_args()
    wanted = set(args.only.split(",")) if args.only else None
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ["PATH"])

    with tempfile.TemporaryDirectory() as tmp:
        tree = Path(tmp) / "project"
        tree.mkdir()
        copy_project(tree)
        build = ["lake", "build", "Dahlias"]
        if subprocess.run(build, cwd=tree, env=env, capture_output=True).returncode != 0:
            sys.exit("the unmutated project does not build")
        survivors = []
        for name, description, edits in MUTANTS:
            if wanted is not None and name not in wanted:
                continue
            saved = {}
            for path, old, new in edits:
                src = (tree / path).read_text()
                saved.setdefault(path, src)
                if src.count(old) != 1:
                    sys.exit(f"{name}: expected one occurrence in {path}, found {src.count(old)}")
                (tree / path).write_text(src.replace(old, new))
            r = subprocess.run(build, cwd=tree, env=env, capture_output=True, text=True)
            for path, src in saved.items():
                (tree / path).write_text(src)
            if r.returncode == 0:
                print(f"{name}: {description}\n    builds", flush=True)
                survivors.append(name)
            else:
                where = failures(tree, r.stdout + r.stderr) or ["an unknown place"]
                print(f"{name}: {description}\n    fails in {', '.join(where)}", flush=True)
        print(f"survivors: {', '.join(survivors) or 'none'}")
        sys.exit(1 if survivors else 0)


if __name__ == "__main__":
    main()
