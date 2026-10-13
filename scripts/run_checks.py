#!/usr/bin/env python3
"""Resource-guarded compatibility checks; no publication or platform API calls."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile
import time
from check_candidate import check
from make_candidate import read_json

TARGET = "Erdos488.Geometry.SeparatedDistances.FixedDimension.fixed_dimension_erdos_670"
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
DEPENDENCY_URLS = {
    "https://github.com/leanprover-community/" + name
    for name in ["mathlib4", "plausible", "LeanSearchClient", "import-graph",
                 "ProofWidgets4", "aesop", "quote4", "batteries"]
} | {"https://github.com/leanprover/lean4-cli"}


def disk(path, minimum_gib):
    free = shutil.disk_usage(path).free
    print(f"Free disk: {free / 2**30:.2f} GiB; required: {minimum_gib} GiB", flush=True)
    if free < minimum_gib * 2**30:
        raise RuntimeError("Host capacity blocker: insufficient disk; no automatic system cleanup")


def run(command, cwd, capture=False):
    disk(cwd, 2)
    print("+ " + " ".join(map(str, command)), flush=True)
    with tempfile.TemporaryFile(mode="w+") as output:
        process = subprocess.Popen(command, cwd=cwd, start_new_session=True,
                                   stdout=output if capture else None,
                                   stderr=subprocess.STDOUT if capture else None)
        try:
            while process.poll() is None:
                if shutil.disk_usage(cwd).free < 2 * 2**30:
                    raise RuntimeError("Host capacity blocker: free disk fell below 2 GiB")
                time.sleep(3)
        except BaseException:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=15)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise
        output.seek(0)
        text = output.read()
        if text:
            print(text, end="", flush=True)
        if process.returncode:
            raise RuntimeError(f"Command exited {process.returncode}: {command}")
        return text


def dependencies(candidate, fetch):
    lock = json.loads((candidate / "lake-manifest.json").read_text())
    if len(lock["packages"]) != 9:
        raise ValueError("Expected nine exact dependency revisions")
    for dep in lock["packages"]:
        if dep["url"] not in DEPENDENCY_URLS or not re.fullmatch(r"[0-9a-f]{40}", dep["rev"]):
            raise ValueError("Unapproved dependency source or mutable revision")
        if not re.fullmatch(r"[A-Za-z0-9_-]+", dep["name"]):
            raise ValueError("Unsafe dependency name")
        directory = candidate / ".lake/packages" / dep["name"]
        if fetch:
            directory.mkdir(parents=True, exist_ok=False)
            run(["git", "init", "--quiet", str(directory)], candidate)
            run(["git", "-C", str(directory), "remote", "add", "origin", dep["url"]], candidate)
            run(["git", "-C", str(directory), "fetch", "--quiet", "--depth=1", "origin", dep["rev"]], candidate)
            run(["git", "-C", str(directory), "-c", "advice.detachedHead=false", "checkout", "--quiet", "--detach", dep["rev"]], candidate)
        head = subprocess.check_output(["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=all"], text=True)
        if head != dep["rev"] or dirty:
            raise RuntimeError("Dependency revision/cleanliness mismatch: " + dep["name"])
        print(f"Dependency: {dep['name']} {head} {dep['url']}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("platform", choices=["palomar", "prove2me"])
    parser.add_argument("phase", choices=["dependencies", "cache", "build", "axioms", "comparator"])
    parser.add_argument("candidate", type=Path)
    args = parser.parse_args()
    candidate = args.candidate.resolve()
    check(args.platform, candidate, allow_build=True)
    expected_version = (candidate / "lean-toolchain").read_text().strip().split(":v", 1)[1]
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    print(version, flush=True)
    if not re.search(r"\bversion " + re.escape(expected_version) + r"(?:,|\s|\))", version):
        raise RuntimeError("Wrong Lean toolchain")
    dependencies(candidate, fetch=args.phase == "dependencies")
    rows = read_json("SOURCE_MANIFEST.json")["modules"]
    if args.phase == "cache":
        disk(candidate, 6)
        imports = sorted({name for row in rows for name in row["imports"] if name.startswith("Mathlib.")})
        run(["lake", "exe", "cache", "--repo=leanprover-community/mathlib4",
             "--cache-from=master,legacy", "get", *imports], candidate)
        disk(candidate, 3)
    elif args.phase == "build":
        if args.platform == "palomar":
            run(["lake", "--no-cache", "build", "Challenge"], candidate)
        for row in rows:
            run(["lake", "--no-cache", "build", row["module"]], candidate)
        run(["lake", "--no-cache", "build"], candidate)
    elif args.phase == "axioms":
        output = run(["lake", "env", "lean", "--trust=0", "AxiomAudit.lean"], candidate, capture=True)
        match = re.search(re.escape(TARGET) + r".*?depends on axioms:\s*\[([^\]]*)\]", output, re.S)
        if not match or {x.strip() for x in match.group(1).split(",") if x.strip()} - ALLOWED_AXIOMS:
            raise RuntimeError("Missing target axiom report or non-permitted axiom")
    elif args.phase == "comparator":
        if args.platform != "palomar":
            raise RuntimeError("Only the Palomar target has a Comparator challenge")
        disk(candidate, 3)
        run(["lake", "comparator", "--config", "comparator.json"], candidate)
    check(args.platform, candidate, allow_build=True)
    dependencies(candidate, fetch=False)
    print(f"PASS: {args.platform} {args.phase}; source/config bytes and dependency pins unchanged", flush=True)


if __name__ == "__main__":
    main()
