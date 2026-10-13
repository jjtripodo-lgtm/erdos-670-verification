#!/usr/bin/env python3
"""Check the complete public wrapper file inventory without executing its tools."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import re


def check(root):
    root = Path(root)
    manifest = root / "PAYLOAD_SHA256.json"
    expected = json.loads(manifest.read_text())
    if not isinstance(expected, dict) or not expected:
        raise ValueError("Expected nonempty exact payload manifest")
    for name, digest in expected.items():
        p = PurePosixPath(name)
        if p.is_absolute() or ".." in p.parts or str(p) != name or name == "PAYLOAD_SHA256.json":
            raise ValueError("Unsafe/self-referential manifest path")
        if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise ValueError("Invalid payload digest")
    actual = {}
    for path in root.rglob("*"):
        relative = path.relative_to(root)
        if path.is_symlink():
            raise ValueError("Payload symlink is forbidden")
        if not path.is_dir() and not path.is_file():
            raise ValueError("Payload special file is forbidden")
        if relative.parts[0] == ".git":
            continue
        if "__pycache__" in relative.parts or path.suffix == ".pyc":
            raise ValueError("Python bytecode/cache content is forbidden in the public wrapper")
        if path.is_file() and relative.as_posix() != "PAYLOAD_SHA256.json":
            actual[relative.as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        bad = sorted(k for k in actual.keys() | expected.keys() if actual.get(k) != expected.get(k))
        raise ValueError("Wrapper file/hash mismatch: " + ", ".join(bad))
    print(f"PASS: exact wrapper inventory, {len(actual) + 1} files")


if __name__ == "__main__":
    check(Path(__file__).resolve().parents[1])
