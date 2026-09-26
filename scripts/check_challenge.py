#!/usr/bin/env python3
"""Check that Challenge.lean repeats the statement module word for word.

The imports of `Challenge.lean` must equal those of `PeterfalviProblem/Statement.lean`, and its
namespace must begin with the definitions of the statement module, unchanged. Comparator checks
the elaborated definitions; this script catches textual drift early.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from gen_challenge import CHALLENGE, NAMESPACE_OPEN, STATEMENT, THEOREMS_MARKER, split_statement


def main() -> int:
    imports, definitions = split_statement(STATEMENT.read_text(encoding="utf-8"))
    challenge = CHALLENGE.read_text(encoding="utf-8")
    challenge_imports = "".join(
        line + "\n" for line in challenge.splitlines() if line.startswith("import "))
    errors = []
    if challenge_imports != imports:
        errors.append("the imports differ from PeterfalviProblem/Statement.lean")
    body = challenge[challenge.index(NAMESPACE_OPEN) + len(NAMESPACE_OPEN):]
    if not body.startswith(definitions + "\n" + THEOREMS_MARKER):
        errors.append("the definitions differ from PeterfalviProblem/Statement.lean")
    for error in errors:
        print(f"error: Challenge.lean: {error}", file=sys.stderr)
    if not errors:
        print("Challenge.lean repeats the statement module word for word.")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
