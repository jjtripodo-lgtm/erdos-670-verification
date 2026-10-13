import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import check_payload
import fetch_upstream


class SupportTests(unittest.TestCase):
    def make_root(self, root):
        (root / "source.txt").write_text("public fixture\n")
        (root / "PAYLOAD_SHA256.json").write_text(json.dumps({"source.txt": hashlib.sha256((root / "source.txt").read_bytes()).hexdigest()}))

    def test_exact_inventory(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.make_root(root)
            check_payload.check(root)

    def test_extra_file_fails(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.make_root(root)
            (root / "unexpected.txt").write_text("x")
            with self.assertRaises(ValueError):
                check_payload.check(root)

    def test_hash_drift_fails(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.make_root(root)
            (root / "source.txt").write_text("changed")
            with self.assertRaises(ValueError):
                check_payload.check(root)

    def test_symlink_fails(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.make_root(root)
            (root / "link").symlink_to(root / "source.txt")
            with self.assertRaises(ValueError):
                check_payload.check(root)

    def test_parent_path_fails(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "PAYLOAD_SHA256.json").write_text(json.dumps({"../outside": "0" * 64}))
            with self.assertRaises(ValueError):
                check_payload.check(root)

    def test_cache_named_directory_fails(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.make_root(root)
            (root / "extraction/__pycache__").mkdir(parents=True)
            (root / "extraction/__pycache__/hidden.pyc").write_bytes(b"unexpected")
            with self.assertRaises(ValueError):
                check_payload.check(root)

    def test_cache_named_symlink_fails(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.make_root(root)
            (root / "__pycache__").symlink_to(root / "source.txt")
            with self.assertRaises(ValueError):
                check_payload.check(root)

    def test_git_named_symlink_fails(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.make_root(root)
            (root / ".git").symlink_to(root / "source.txt")
            with self.assertRaises(ValueError):
                check_payload.check(root)

    def test_fetch_rejects_hash_drift(self):
        class Response:
            def __enter__(self): return self
            def __exit__(self, *args): return None
            def read(self, _): return b"not the official bytes"
        with tempfile.TemporaryDirectory() as d, patch.object(fetch_upstream, "urlopen", return_value=Response()):
            with self.assertRaises(ValueError):
                fetch_upstream.fetch(Path(d) / "new")

    def test_fetch_rejects_existing_directory(self):
        with tempfile.TemporaryDirectory() as d, patch.object(fetch_upstream, "urlopen") as mocked:
            with self.assertRaises(FileExistsError):
                fetch_upstream.fetch(Path(d))
            mocked.assert_not_called()


if __name__ == "__main__":
    unittest.main()
