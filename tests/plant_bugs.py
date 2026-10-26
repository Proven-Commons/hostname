#!/usr/bin/env python3
"""Check that the differential tests catch planted bugs.

Each bug is a one-line change to Hostname/Basic.lean. The script
copies the project to a temporary folder, plants one bug at a time,
runs tests/run_tests.py there with a small count, and records how many
failures the tests report. Every planted bug must give at least one.
The unchanged copy must give none. Each bug also breaks a proof, so
`lake build` of the whole project fails with it in place; the tests
build only the executable, so they run.

    python3 tests/plant_bugs.py [--count N]

The script writes tests/PLANTED-BUGS.md and exits non-zero if any bug
goes uncaught.
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "tests" / "PLANTED-BUGS.md"
CODE = "Hostname/Basic.lean"

# (what the bug does, the line as written, the line with the bug)
BUGS = [
    ("lower case misses Z",
     "if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c",
     "if 'A' ≤ c && c ≤ 'Y' then Char.ofNat (c.toNat + 32) else c"),
    ("a wildcard over one label is allowed",
     "| some s => s.length ≤ 251 && validName s && s.contains '.'",
     "| some s => s.length ≤ 251 && validName s"),
    ("a label may end in a hyphen",
     "| some a, some b => l.length ≤ 63 && isLetDig a && isLetDig b && l.all isLDH",
     "| some a, some _ => l.length ≤ 63 && isLetDig a && l.all isLDH"),
    ("a wildcard may stand for no label",
     "| some rest => sameIgnoringCase rest s",
     "| some rest => sameIgnoringCase rest s || sameIgnoringCase (dropDot reference.toList) s"),
    ("a name of 254 characters is allowed",
     "cs.length ≤ 253 && (cs.splitOn '.').all validLabel",
     "cs.length ≤ 254 && (cs.splitOn '.').all validLabel"),
    ("a wildcard name of 254 characters is allowed",
     "| some s => s.length ≤ 251 && validName s && s.contains '.'",
     "| some s => s.length ≤ 252 && validName s && s.contains '.'"),
    ("an all-digit last label is allowed",
     "cs.length ≤ 253 && (cs.splitOn '.').all validLabel && lastNotNumeric (cs.splitOn '.')",
     "cs.length ≤ 253 && (cs.splitOn '.').all validLabel"),
    ("every trailing dot is dropped",
     "if cs.getLast? = some '.' then cs.dropLast else cs",
     "if cs.getLast? = some '.' then (cs.reverse.dropWhile (· = '.')).reverse else cs"),
    ("case is not ignored",
     "a.map lowerAscii == b.map lowerAscii",
     "a == b"),
    ("a label of 64 characters is allowed",
     "| some a, some b => l.length ≤ 63 && isLetDig a && isLetDig b && l.all isLDH",
     "| some a, some b => l.length ≤ 64 && isLetDig a && isLetDig b && l.all isLDH"),
]


def failures(copy, count):
    """The failures a run of the tests reports, or None, with the run's
    output, when it reports none: the code did not build, or the run did
    not finish. A run that dies writes no record, so the old one is
    removed first rather than read again."""
    record = copy / "tests" / "TEST-RESULTS.md"
    record.unlink(missing_ok=True)
    run = subprocess.run([sys.executable, "tests/run_tests.py", "--count", str(count)],
                         cwd=copy, capture_output=True, text=True)
    out = run.stdout + run.stderr
    if not record.exists():
        return None, f"no record written, exit status {run.returncode}\n{out}"
    m = re.search(r"^- Failures: (\d+)(.*)$", record.read_text(encoding="utf-8"), re.M)
    if m is None or "build" in m.group(2):
        return None, out  # the bug did not build: not a catch
    n = int(m.group(1))
    if run.returncode != (1 if n else 0):
        return None, f"{n} failures but exit status {run.returncode}\n{out}"
    return n, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=2000)
    args = ap.parse_args()
    rows, missed = [], 0
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / "hostname"
        shutil.copytree(ROOT, copy, symlinks=True,
                        ignore=shutil.ignore_patterns("PLANTED-BUGS.md"))
        code = copy / CODE
        original = code.read_text(encoding="utf-8")
        n, err = failures(copy, args.count)
        rows.append(("none", n))
        if n != 0:
            missed += 1
        for what, line, bug in BUGS:
            if original.count(line) != 1:
                sys.exit(f"{CODE} no longer holds, once, the line for {what!r}: {line}")
            code.write_text(original.replace(line, bug), encoding="utf-8")
            n, err = failures(copy, args.count)
            code.write_text(original, encoding="utf-8")
            rows.append((what, n))
            if not n:
                missed += 1
            print(f"{what}: {n} failures" + (" (did not build or did not finish)" if err else ""))
    lines = ["# Planted bugs", "",
             "Written by `tests/plant_bugs.py`. Each bug is a one-line change to "
             f"`{CODE}`, tested with `tests/run_tests.py --count {args.count}`. "
             "Every bug must give failures, and the unchanged code none.", "",
             "| Planted bug | Failures |", "|---|---|"]
    lines += [f"| {what} | {'did not build or did not finish' if n is None else n} |" for what, n in rows]
    lines += ["", f"Bugs caught: {sum(1 for what, n in rows[1:] if n)} of {len(BUGS)}", ""]
    RECORD.write_text("\n".join(lines), encoding="utf-8")
    return 1 if missed else 0


if __name__ == "__main__":
    sys.exit(main())
