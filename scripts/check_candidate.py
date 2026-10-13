#!/usr/bin/env python3
"""Offline exact-file verification, including a code-only allowlist."""
import argparse
import json
from pathlib import Path
from make_candidate import ROOT, digest, read_json


def check(platform, candidate, allow_build=False):
    expected = {row["path"]: row[platform + "_sha256"]
                for row in read_json("SOURCE_MANIFEST.json")["modules"]}
    for name, sha in read_json("FIXTURE_SHA256.json").items():
        if name.startswith(platform + "/"):
            expected[name.split("/", 1)[1].removesuffix(".txt")] = sha
    actual = {}
    for path in candidate.rglob("*"):
        relative = path.relative_to(candidate)
        if allow_build and relative.parts[0] == ".lake":
            continue
        if path.is_symlink():
            raise ValueError("Unexpected symlink: " + str(relative))
        if path.is_file():
            actual[str(relative)] = digest(path.read_bytes())
    if actual != expected:
        bad = sorted(key for key in actual.keys() | expected.keys()
                     if actual.get(key) != expected.get(key))
        raise ValueError("Candidate file/hash mismatch: " + ", ".join(bad))
    result = {"platform": platform, "files": len(expected), "sha256": actual}
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("platform", choices=["palomar", "prove2me"])
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--allow-build", action="store_true")
    args = parser.parse_args()
    check(args.platform, args.candidate, args.allow_build)
