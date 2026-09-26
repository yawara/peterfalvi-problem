#!/usr/bin/env python3
"""Run the checks of this repository: metadata, build, lint, and the axiom audit.

Copyright (c) 2026 Yawara Ishida. Released under Apache-2.0; see LICENSE.

Every step must succeed with no warnings. The only exception is the Challenge build, which must
report exactly its two deliberate `sorry` holes. Logs and a summary are written to `.audit/`.
The Comparator comparison is separate: see `scripts/verify-comparator.sh`.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / ".audit"
ANSI = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")
WARNING = re.compile(r"(^|\s)warning:|⚠", re.MULTILINE)
SORRY_WARNING = re.compile(r"^warning: Challenge\.lean:\d+:\d+: declaration uses `sorry`$",
                           re.MULTILINE)
# Lake marks a module that logged warnings with a `⚠` progress line.
CHALLENGE_MARKER = re.compile(r"^⚠ \[\d+/\d+\] (?:Built|Replayed) Challenge\b", re.MULTILINE)
LEAN_TEST_OPTIONS = [
    "-DautoImplicit=false", "-Dlinter.mathlibStandardSet=true",
    "-Dlinter.style.header=true", "-Dlinter.style.longFile=1500",
    "-DwarningAsError=true",
]
CHALLENGE_HOLES = 2


def source_hashes() -> dict[str, str]:
    """Record the inputs, so that a change during the run is detected."""
    files = [ROOT / name for name in [
        "PeterfalviProblem.lean", "Challenge.lean", "Solution.lean", "lean-toolchain",
        "lakefile.toml", "lake-manifest.json", "formalization.yaml", "comparator.json",
        "requirements-palomar.txt", "LICENSE",
    ]]
    for directory, suffix in [("PeterfalviProblem", ".lean"), ("Tests", ".lean"),
                              ("scripts", ".py"), ("scripts", ".sh"), ("scripts", ".json")]:
        files.extend((ROOT / directory).rglob(f"*{suffix}"))
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(files)}


def run_step(name: str, command: list[str], env: dict[str, str],
             allowed_warnings: re.Pattern[str] | None = None, expected: int = 0) -> dict:
    print(f"[{name}] {' '.join(command)}", flush=True)
    started = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
    output = ANSI.sub("", result.stdout)
    (AUDIT / f"{name}.log").write_text(output, encoding="utf-8")
    warnings = len(WARNING.findall(output))
    allowed = len(allowed_warnings.findall(output)) if allowed_warnings else 0
    markers = len(CHALLENGE_MARKER.findall(output)) if allowed_warnings else 0
    record = {"name": name, "command": command, "exit_code": result.returncode,
              "warnings": warnings, "allowed_warnings": allowed,
              "seconds": round(time.monotonic() - started, 3)}
    record["passed"] = (result.returncode == 0 and allowed == expected
                        and warnings == allowed + markers)
    if record["passed"]:
        print(f"[{name}] passed ({record['seconds']}s)", flush=True)
    else:
        print(output[-16000:], end="", flush=True)
        print(f"[{name}] FAILED: exit={result.returncode}, warnings={warnings}, "
              f"expected sorry warnings={expected}, found={allowed}", flush=True)
    return record


def main() -> int:
    AUDIT.mkdir(exist_ok=True)
    env = os.environ.copy()
    env["NO_COLOR"] = "1"
    before = source_hashes()
    report = {"schema_version": 1, "inputs": before, "steps": [], "passed": False}
    report_path = AUDIT / "checks.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    lean_test = ["lake", "env", "lean", *LEAN_TEST_OPTIONS]
    steps = [
        ("palomar-metadata", [sys.executable, "scripts/check_palomar_metadata.py"], None, 0),
        ("challenge-text", [sys.executable, "scripts/check_challenge.py"], None, 0),
        ("build", ["lake", "build"], None, 0),
        ("challenge-build", ["lake", "build", "Challenge"], SORRY_WARNING, CHALLENGE_HOLES),
        ("imports", ["lake", "exe", "mk_all", "--check", "--lib", "PeterfalviProblem"], None, 0),
        ("environment-lint", ["lake", "lint", "--", "--no-build", "PeterfalviProblem"], None, 0),
        ("text-lint", [*lean_test, "Tests/TextLint.lean"], None, 0),
        ("axioms", [*lean_test, "Tests/Axioms.lean"], None, 0),
    ]
    for name, command, allowed, expected in steps:
        record = run_step(name, command, env, allowed, expected)
        report["steps"].append(record)
        report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        if not record["passed"]:
            return 1
    report["inputs_unchanged"] = before == source_hashes()
    report["passed"] = report["inputs_unchanged"]
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if not report["passed"]:
        print("The inputs changed during the checks; run them again.", file=sys.stderr)
        return 1
    print("All checks passed; report: .audit/checks.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
