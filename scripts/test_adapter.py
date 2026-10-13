#!/usr/bin/env python3
"""Offline adapter tests. Optional --source-root checks all 54 actual sources."""
import argparse
import contextlib
import io
import json
from pathlib import Path
import re
import tempfile
import unittest
from check_candidate import check
from make_candidate import ROOT, COMMIT, REPOSITORY, digest, generate, migrate, read_json, safe_path


class AdapterTests(unittest.TestCase):
    source_root = None

    def test_payload_manifest(self):
        expected = read_json("PAYLOAD_SHA256.json")
        for name, sha in expected.items():
            safe_path(name)
            self.assertEqual(digest((ROOT / name).read_bytes()), sha, name)

    def test_source_manifest(self):
        manifest = read_json("SOURCE_MANIFEST.json")
        self.assertEqual(manifest["source_repository"], REPOSITORY)
        self.assertEqual(manifest["source_commit"], COMMIT)
        self.assertEqual(manifest["module_count"], 54)
        self.assertEqual(len(manifest["modules"]), 54)
        self.assertEqual(len({r["path"] for r in manifest["modules"]}), 54)
        shared = {p["path"] for p in read_json("PALOMAR_MIGRATION_PATCHES.json")
                  if "prove2me" in p["platforms"]}
        self.assertEqual(shared, {"Erdos488/Geometry/SeparatedDistances/PrefixSums.lean"})
        for row in manifest["modules"]:
            safe_path(row["path"])
            if row["path"] in shared:
                self.assertNotEqual(row["source_sha256"], row["prove2me_sha256"])
            else:
                self.assertEqual(row["source_sha256"], row["prove2me_sha256"])
            for key in ["source_sha256", "palomar_sha256", "prove2me_sha256"]:
                self.assertRegex(row[key], r"^[0-9a-f]{64}$")

    def test_migration(self):
        source = "import Mathlib.Tactic\nimport Foo\n\ntheorem test : True := by trivial\n"
        expected = ("module\n\npublic import Mathlib.Tactic\npublic import Foo\n"
                    "\n@[expose] public section\n\ntheorem test : True := by trivial\n")
        self.assertEqual(migrate(source), expected)
        self.assertEqual(len(read_json("PALOMAR_MIGRATION_PATCHES.json")), 3)

    def test_paths_fail_closed(self):
        for value in ["/etc/passwd", "../file", "a/../file", "a//file"]:
            with self.assertRaises(ValueError):
                safe_path(value)

    def test_fixtures(self):
        fixture_hashes = read_json("FIXTURE_SHA256.json")
        paths = {str(p.relative_to(ROOT / "fixtures")) for p in (ROOT / "fixtures").rglob("*") if p.is_file()}
        self.assertEqual(paths, set(fixture_hashes))
        self.assertEqual(len(paths), 13)
        self.assertFalse(list((ROOT / "fixtures").rglob("*.lean")))
        for path, expected in fixture_hashes.items():
            self.assertEqual(digest((ROOT / "fixtures" / path).read_bytes()), expected)
        for platform in ["palomar", "prove2me"]:
            lock = json.loads((ROOT / "fixtures" / platform / "lake-manifest.json").read_text())
            self.assertEqual(len(lock["packages"]), 9)
            self.assertTrue(all(re.fullmatch(r"[0-9a-f]{40}", p["rev"]) for p in lock["packages"]))
        self.assertIn("autoImplicit = false", (ROOT / "fixtures/prove2me/lakefile.toml").read_text())

    def test_workflow_constraints(self):
        workflow = (ROOT / ".github/workflows/compatibility.yml").read_text()
        self.assertIn("runs-on: ubuntu-22.04", workflow)
        self.assertIn("contents: read", workflow)
        self.assertIn("github.event.repository.private == false", workflow)
        self.assertIn("platform: [palomar, prove2me]", workflow)
        # GitHub resolves job-level env before runner contexts exist.
        before_steps = workflow.split("    steps:", 1)[0]
        self.assertNotIn("runner.", before_steps)
        for assignment in ["MATHLIB_CACHE_DIR=$RUNNER_TEMP/mathlib-cache",
                           "LAKE_CACHE_DIR=$RUNNER_TEMP/lake-cache",
                           "COMPARATOR_BWRAP=$RUNNER_TEMP/bwrap-bin/bwrap"]:
            self.assertIn(assignment, workflow)
        self.assertIn('} >> "$GITHUB_ENV"', workflow)
        for forbidden in ["secrets.", "uses:", "upload-artifact", "pull_request_target", "container:"]:
            self.assertNotIn(forbidden, workflow)
        scripts = "\n".join(p.read_text() for p in (ROOT / "scripts").glob("*") if p.suffix in {".py", ".sh"} and p.name != "test_adapter.py")
        self.assertNotIn("--inadvisably-no-" + "sandbox", scripts)
        self.assertNotIn("sudo sysctl", scripts)
        self.assertNotIn("apparmor_parser", scripts)

    def test_actual_generation_and_tamper_rejection(self):
        if self.source_root is None:
            self.skipTest("Pass --source-root for the offline 54-module integration check")
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for platform, count in [("palomar", 62), ("prove2me", 59)]:
                candidate = root / platform
                result = generate(platform, candidate, self.source_root)
                self.assertEqual(result["candidate_files"], count)
                with contextlib.redirect_stdout(io.StringIO()):
                    check(platform, candidate)
                first = read_json("SOURCE_MANIFEST.json")["modules"][0]["path"]
                with (candidate / first).open("a") as stream:
                    stream.write("\n-- unexpected mutation\n")
                with self.assertRaises(ValueError):
                    check(platform, candidate)
                (candidate / "unexpected.pdf").write_bytes(b"unexpected")
                with self.assertRaises(ValueError):
                    check(platform, candidate)
            # A source-byte mismatch must fail before creating any destination.
            first = read_json("SOURCE_MANIFEST.json")["modules"][0]["path"]
            source = root / "bad-source" / first
            source.parent.mkdir(parents=True)
            source.write_bytes(b"wrong bytes")
            destination = root / "rejected"
            with self.assertRaises(ValueError):
                generate("palomar", destination, root / "bad-source")
            self.assertFalse(destination.exists())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path)
    args = parser.parse_args()
    AdapterTests.source_root = args.source_root
    unittest.main(argv=["test_adapter.py"], verbosity=2)
