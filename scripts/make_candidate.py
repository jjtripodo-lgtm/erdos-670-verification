#!/usr/bin/env python3
"""Reproduce a code-only candidate from immutable public source and fixtures."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "jjtripodo-lgtm/erdos-670-fixed-dimension"
COMMIT = "1e73a12ff1076dd11affadbf619ddbbef587133e"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_json(name):
    return json.loads((ROOT / name).read_text(encoding="utf-8"))


def migrate(text):
    lines = text.splitlines(keepends=True)
    last = max(i for i, line in enumerate(lines) if line.startswith("import "))
    lines = ["public " + line if line.startswith("import ") else line for line in lines]
    lines.insert(last + 1, "\n@[expose] public section\n")
    return "module\n\n" + "".join(lines)


def safe_path(value):
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or str(path) != value:
        raise ValueError("Unsafe relative path: " + value)
    return path


def generate(platform, output, source_root=None):
    manifest = read_json("SOURCE_MANIFEST.json")
    if (manifest["source_repository"], manifest["source_commit"], manifest["module_count"]) != (REPOSITORY, COMMIT, 54):
        raise ValueError("Unexpected source identity")
    rows = manifest["modules"]
    if len(rows) != 54 or len({row["path"] for row in rows}) != 54:
        raise ValueError("Expected 54 distinct modules")
    patches = read_json("PALOMAR_MIGRATION_PATCHES.json")
    if len(patches) != 3:
        raise ValueError("Expected exactly three migration edits")
    files = {}
    for row in rows:
        path = safe_path(row["path"])
        if not str(path).startswith("Erdos488/") or path.suffix != ".lean":
            raise ValueError("Unexpected source path")
        if source_root is None:
            url = f"https://raw.githubusercontent.com/{REPOSITORY}/{COMMIT}/lean-fixed670/{path}"
            with urllib.request.urlopen(url, timeout=90) as response:
                data = response.read(2 * 1024 * 1024)
        else:
            source = source_root / path
            if source.is_symlink():
                raise ValueError("Source symlinks are not allowed")
            data = source.read_bytes()
        if digest(data) != row["source_sha256"]:
            raise ValueError("Source hash mismatch: " + str(path))
        if platform == "palomar":
            text = migrate(data.decode("utf-8"))
            for patch in patches:
                if patch["path"] == str(path):
                    if text.count(patch["old"]) != 1:
                        raise ValueError("Migration edit does not match once: " + str(path))
                    text = text.replace(patch["old"], patch["new"], 1)
            data = text.encode("utf-8")
        if digest(data) != row[platform + "_sha256"]:
            raise ValueError("Candidate hash mismatch: " + str(path))
        files[str(path)] = data
    fixture_hashes = read_json("FIXTURE_SHA256.json")
    for name, expected in fixture_hashes.items():
        path = safe_path(name)
        if path.parts[0] != platform:
            continue
        source = ROOT / "fixtures" / path
        if source.is_symlink():
            raise ValueError("Fixture symlinks are not allowed")
        data = source.read_bytes()
        if digest(data) != expected:
            raise ValueError("Fixture hash mismatch: " + name)
        files[str(PurePosixPath(*path.parts[1:])).removesuffix(".txt")] = data
    # Validate every byte before creating the destination. Never overwrite a tree.
    output.mkdir(parents=True, exist_ok=False)
    for name, data in files.items():
        target = output / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    return {"platform": platform, "source_commit": COMMIT, "source_modules": 54,
            "candidate_files": len(files), "source_and_fixture_hashes": "PASS"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("platform", choices=["palomar", "prove2me"])
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--source-root", type=Path,
                        help="Offline source root containing Erdos488; otherwise fetch only the pinned 54 public files")
    args = parser.parse_args()
    print(json.dumps(generate(args.platform, args.output, args.source_root), indent=2))


if __name__ == "__main__":
    main()
