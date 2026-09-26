#!/usr/bin/env python3
"""Check the Palomar metadata of this repository offline.

Copyright (c) 2026 Yawara Ishida. Released under Apache-2.0; see LICENSE.

The check validates `formalization.yaml` against the pinned v0.4 schema, applies the mechanical
rules of the Palomar submission policy that can be checked offline, and compares the metadata
with `comparator.json` and the Lean sources. It is not a Palomar review. Install the pinned
Python dependencies with `requirements-palomar.txt`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

import yaml
from jsonschema.validators import validator_for


ROOT = Path(__file__).resolve().parents[1]
SCHEMAS = Path(__file__).resolve().parent / "palomar-schema"
PINNED_INPUTS = {
    "v0.4.schema.json": "25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce",
    "LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
    "arxiv-codes.json": "aca149ce8d56144aebd1d12ff0bfbe67bd412f36b8401a88704635ff20c24911",
    "msc2020-codes.json": "711221fc1a61ac16efd153086836dc3e6debd256de0aef5b41616e75ea4b0333",
    "PALOMAR-LICENSE": "10321b0cca2b8025d4b5065dd20e22c1f74da2e872c12363e3601974e093bc21",
}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MAIN_FILE = "PeterfalviProblem/Main.lean"
MAIN_MODULE = "PeterfalviProblem.Main"
RESULTS = {"PeterfalviProblem.not_hypothesisB_three", "PeterfalviProblem.hypothesisB_two"}
RELATIONSHIPS = {"formalizes", "adapts", "independently-proves", "background", "other"}
SOURCE_TYPES = {"paper", "book", "web discussion", "folklore", "original-proof", "other"}
METHODS = {"manual", "copilot", "agent", "autonomous", "other"}
LICENSE_NAME = re.compile(r"(?:licen[cs]e|copying|unlicense|ofl)(?:\.(?:md|markdown|txt))?", re.I)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def unique_pairs(pairs: list[tuple]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate mapping key: {key!r}")
        result[key] = value
    return result


class MetadataLoader(yaml.SafeLoader):
    """Ordinary YAML, without duplicate keys or merge keys."""


def unique_yaml_mapping(loader: MetadataLoader, node: yaml.MappingNode) -> dict:
    require(all(key.tag != "tag:yaml.org,2002:merge" for key, _ in node.value),
            "YAML merge keys are not accepted")
    return unique_pairs([(loader.construct_object(key), loader.construct_object(value))
                         for key, value in node.value])


MetadataLoader.add_constructor("tag:yaml.org,2002:map", unique_yaml_mapping)


def regular_file(root: Path, relative: str) -> Path:
    path = root / relative
    require(path.resolve().is_relative_to(root.resolve()), f"path escapes repository: {relative}")
    require(path.is_file() and not path.is_symlink(), f"not a regular file: {relative}")
    return path


def nonempty_text(value: object, label: str, maximum: int | None = None) -> None:
    require(isinstance(value, str) and bool(value.strip()), f"{label} must be nonempty text")
    require(maximum is None or len(value) <= maximum, f"{label} exceeds {maximum} characters")


def distinct_strings(value: object, label: str, minimum: int, maximum: int) -> None:
    require(isinstance(value, list) and minimum <= len(value) <= maximum,
            f"{label} must contain {minimum}-{maximum} entries")
    for entry in value:
        nonempty_text(entry, label)
    require(len(value) == len(set(value)), f"{label} contains duplicates")


def check_metadata(root: Path, data: dict) -> None:
    schema = json.loads((SCHEMAS / "v0.4.schema.json").read_text(encoding="utf-8"))
    validator = validator_for(schema)
    validator.check_schema(schema)
    errors = list(validator(schema).iter_errors(data))
    require(not errors, "schema errors: " + "; ".join(
        f"{'.'.join(map(str, error.absolute_path))}: {error.message}" for error in errors))
    require(data.get("version") == "v0.4", "metadata must declare version: v0.4")
    require("repository" not in data, "this repository is the substantive development")

    project = data["project"]
    nonempty_text(project["name"], "project.name", 300)
    nonempty_text(project.get("description"), "project.description", 10000)
    for field in ("authors", "responsible_maintainers"):
        distinct_strings(project.get(field), f"project.{field}", 1, 1000)
    require(project["license"] == "Apache-2.0", "the project declares Apache-2.0")
    license_files = [path for path in root.iterdir() if LICENSE_NAME.fullmatch(path.name)]
    require(len(license_files) == 1, "the repository root must have exactly one license file")
    license_text = regular_file(root, license_files[0].name).read_bytes().replace(b"\r\n", b"\n")
    require(license_text == (SCHEMAS / "LICENSE").read_bytes(),
            "the root license is not the standard Apache-2.0 text")

    classification = data.get("classification", {})
    for field, minimum in (("arxiv", 1), ("msc2020", 0)):
        codes = classification.get(field, [])
        distinct_strings(codes, f"classification.{field}", minimum, 8)
        known = set(json.loads((SCHEMAS / f"{field}-codes.json").read_text(encoding="utf-8")))
        require(set(codes) <= known, f"unknown {field} classification: {set(codes) - known}")

    methods = data["automation"]["methods"]
    require(isinstance(methods, list) and methods, "automation.methods must be nonempty")
    for method in methods:
        require(method.get("method") in METHODS, "automation.methods[].method is not standard")
    nonempty_text(data["review"]["status"], "review.status")

    sources = data["sources"]
    require(isinstance(sources, list) and sources, "sources must be nonempty")
    for item in sources:
        nonempty_text(item["title"], "sources[].title")
        require(item.get("relationship") in RELATIONSHIPS,
                "sources[].relationship must use a standard category")
        require("type" not in item or item["type"] in SOURCE_TYPES,
                f"sources[].type is not accepted: {item.get('type')!r}")
        for contributor in item.get("contributors", []):
            nonempty_text(contributor.get("name"), "sources[].contributors[].name")
            nonempty_text(contributor.get("role"), "sources[].contributors[].role", 200)
    originals = [item for item in sources if item.get("type") == "original-proof"]
    require(originals, "the result is original, so an original-proof source is required")
    require(all(item["relationship"] == "other" for item in originals),
            "an original-proof source must have relationship: other")
    require(all(item["relationship"] in {"background", "other"} for item in sources),
            "an original result lists other sources only as background or other")
    for item in data.get("related_formalizations", []):
        nonempty_text(item.get("id"), "related_formalizations[].id")
        nonempty_text(item.get("note"), "related_formalizations[].note")


def check_comparator(root: Path) -> dict:
    raw_config = regular_file(root, "comparator.json").read_bytes()
    require(len(raw_config) <= 1024 * 1024, "comparator.json exceeds 1 MiB")
    config = json.loads(raw_config, object_pairs_hook=unique_pairs)
    required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
    require(isinstance(config, dict) and required <= config.keys()
            and config.keys() <= required | {"definition_names", "enable_nanoda"},
            "comparator.json has missing or unsupported keys")
    require(config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution",
            "this project compares the root Challenge and Solution modules")
    challenge = regular_file(root, "Challenge.lean").read_text(encoding="utf-8")
    require(len(challenge.encode("utf-8")) <= 32 * 1024 and challenge.count("\n") <= 300,
            "the Challenge exceeds the size at which Palomar warns")
    regular_file(root, "Solution.lean")
    distinct_strings(config["theorem_names"], "theorem_names", 1, 1000)
    require(set(config["theorem_names"]) == RESULTS, "Comparator must select both main results")
    require(config.get("definition_names", []) == [], "no definition is left unspecified")
    distinct_strings(config["permitted_axioms"], "permitted_axioms", 0, 3)
    require(set(config["permitted_axioms"]) <= AXIOMS, "Comparator permits a nonstandard axiom")
    require(config.get("enable_nanoda") is True, "the local comparison must enable NanoDa")
    return config


def check_results(root: Path, data: dict) -> None:
    status = data.get("status", {})
    require(status.get("sorry_count") == 0 and status.get("sorry_in_definitions") == 0,
            "the proof development must report zero holes")
    require(set(status.get("axioms", [])) == AXIOMS, "status must record the three axioms")
    nonempty_text(status.get("scope"), "status.scope")
    nonempty_text(data.get("fidelity", {}).get("divergences"), "fidelity.divergences")
    main_results = status.get("main_results", [])
    alignment = data.get("alignment", {}).get("statements", [])
    require({item.get("declaration") for item in main_results} == RESULTS
            and len(main_results) == len(RESULTS), "status.main_results must match Comparator")
    require({item.get("lean") for item in alignment} == RESULTS
            and len(alignment) == len(RESULTS), "alignment.statements must match Comparator")
    main = regular_file(root, MAIN_FILE).read_text(encoding="utf-8")
    for item in main_results:
        name = item["declaration"]
        require(item.get("file") == MAIN_FILE and item.get("comparator_config") == "comparator.json",
                f"wrong file or Comparator path for {name}")
        require(item.get("sorry_count") == 0 and set(item.get("axioms", [])) == AXIOMS,
                f"wrong sorry count or axioms for {name}")
        short = name.removeprefix("PeterfalviProblem.")
        require(re.search(rf"^theorem {re.escape(short)}\b", main, re.M) is not None,
                f"{MAIN_FILE} does not declare {name}")
    for item in alignment:
        require(item.get("module") == MAIN_MODULE and item.get("status") == "proved",
                f"wrong alignment module or status for {item.get('lean')}")


def check(root: Path) -> None:
    for name, expected in PINNED_INPUTS.items():
        require(hashlib.sha256((SCHEMAS / name).read_bytes()).hexdigest() == expected,
                f"pinned metadata input changed: {name}")
    source = regular_file(root, "formalization.yaml").read_bytes()
    require(len(source) <= 256 * 1024, "formalization.yaml exceeds 256 KiB")
    data = yaml.load(source.decode("utf-8"), Loader=MetadataLoader)
    require(isinstance(data, dict), "formalization.yaml must contain one mapping")
    check_metadata(root, data)
    check_comparator(root)
    check_results(root, data)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root to check")
    args = parser.parse_args()
    try:
        check(args.root.resolve())
    except (ValueError, TypeError, KeyError, OSError, yaml.YAMLError) as error:
        print(f"Palomar metadata check failed: {error}", file=sys.stderr)
        return 1
    print("Palomar metadata check passed. This is not a Palomar review.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
