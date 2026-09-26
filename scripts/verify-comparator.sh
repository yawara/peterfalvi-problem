#!/usr/bin/env bash
set -euo pipefail

# Compare the Challenge and Solution modules with Comparator, and replay the proofs with Lean's
# kernel, NanoDa and con-ron, all bundled with the selected Lean release.
#
# Originally adapted from PalomarRegistry/PalomarTemplate (Apache-2.0),
# commit 128a6c5ce5f48622e69927ccd639cbff401022e8, scripts/verify-comparator.sh.
# Reference verifier: PalomarRegistry/PalomarSubmission commit
# a59f25bd8a66bf6faf3a4f4260d412989c0185ea, scripts/verify_submission.py.
# This local comparison is not the complete Palomar verification.

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cache_root=${PALOMAR_COMPARATOR_CACHE:-"$repository_root/.cache/palomar-comparator"}

for required_command in git lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run Comparator" >&2
    exit 1
  fi
done

cd "$repository_root"
project_toolchain=$(tr -d '[:space:]' < lean-toolchain)
lean_prefix=$(ELAN_TOOLCHAIN="$project_toolchain" lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$lean_prefix/bin/$tool" ]; then
    echo "error: the selected Lean release does not bundle $tool" >&2
    exit 1
  fi
done

# Palomar's verifier uses bubblewrap 0.12.0. Older distribution packages may lack the sandbox
# fix that it requires.
bwrap_binary=$(command -v "${COMPARATOR_BWRAP:-bwrap}" || true)
if [ -z "$bwrap_binary" ] || [ "$("$bwrap_binary" --version)" != "bubblewrap 0.12.0" ]; then
  echo "error: bubblewrap 0.12.0 is required; set COMPARATOR_BWRAP to its binary" >&2
  echo "see README.md, section 'Building and checking', for the pinned installer" >&2
  exit 1
fi

mkdir -p "$cache_root"
local_config=$(mktemp "$cache_root/comparator.XXXXXX.json")
trap 'rm -f "$local_config"' EXIT
python3 - "$repository_root/comparator.json" "$local_config" "$lean_prefix" <<'PY'
import json
from pathlib import Path
import sys

source, destination, prefix = map(Path, sys.argv[1:])
config = json.loads(source.read_text(encoding="utf-8"))
if not isinstance(config, dict) or config.pop("enable_nanoda", None) is not True:
    raise SystemExit("error: comparator.json must require NanoDa replay")
if "external_kernels" in config:
    raise SystemExit("error: external_kernels belongs only in the generated local configuration")
config["external_kernels"] = {
    "nanoda": [str((prefix / "bin/nanoda_bin").resolve())],
    "con-ron": [str((prefix / "bin/con-ron").resolve())],
}
destination.write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

COMPARATOR_BWRAP="$bwrap_binary" \
  "$lean_prefix/bin/lake" comparator --config "$local_config"
