import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import validate_nodes as v

class NodesTests(unittest.TestCase):
    def test_exact_materialization_and_payload_equality(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'candidate';v.materialize(p);r=v.check(p)
            self.assertEqual(len(r['build_targets']),48)
            self.assertEqual(len([x for x in r['records'] if x['kind']=='theorem_node']),10)
    def test_tampered_candidate_fails(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'candidate';v.materialize(p);(p/'lean-toolchain').write_text('wrong')
            with self.assertRaises(ValueError):v.check(p)
    def test_extra_candidate_file_fails(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'candidate';v.materialize(p);(p/'Extra.lean').write_text('')
            with self.assertRaises(ValueError):v.check(p)
    def test_fresh_directory_required(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaises(ValueError):v.materialize(Path(temp))
    def test_private_original_import_rejected(self):
        self.assertFalse(v.name_ok('X; echo bad'));self.assertFalse(v.name_ok('A.β'))
        self.assertTrue(v.name_ok('Erdos488.A_x'))
    def test_paths_reject_traversal_and_ambiguous_forms(self):
        for name in ['../x','/tmp/x','x/../y','x/./y','x\\y','.','']:
            with self.assertRaises(ValueError):v.safe_path(name)
    def test_inventory_rejects_link_and_cache(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp);(p/'.lake').mkdir()
            with self.assertRaises(ValueError):v.inventory(p)
            self.assertEqual(v.inventory(p,allow_build=True),{})
            (p/'link').symlink_to('/not_read')
            with self.assertRaises(ValueError):v.inventory(p,allow_build=True)
    def test_axiom_reports_parse_only_exact_names(self):
        self.assertEqual(v.axioms("'X.y' depends on axioms: [propext, Classical.choice, Quot.sound]",'X.y'),v.ALLOWED_AXIOMS)
        self.assertEqual(v.axioms("'X.y' does not depend on any axioms",'X.y'),set())
        self.assertEqual(v.axioms("'solution' depends on axioms: [sorryAx]",'solution'),{'sorryAx'})
        with self.assertRaises(ValueError):v.axioms("'X.ya' depends on axioms: [sorryAx]",'X.y')
        with self.assertRaises(ValueError):v.axioms("'X.y' depends on axioms: []\n'X.y' depends on axioms: []",'X.y')
    def test_network_and_build_phases_require_explicit_execution_flag(self):
        with patch('sys.argv',['node-preflight']),tempfile.TemporaryDirectory() as temp:
            with self.assertRaises(ValueError):v.main(['cache','--candidate',temp])

if __name__=='__main__':unittest.main()
