import contextlib
import io
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
    def test_global_solutions_preserve_original_namespace_context(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'candidate';v.materialize(p);r=v.check(p)
            for node in r['records']:
                if node['kind']!='theorem_node':continue
                namespace=node['theorem_name'].rsplit('.',1)[0]
                solution=(p/(node['solution_module'].replace('.','/')+'.lean')).read_text()
                marker='\nnamespace '+namespace+'\n\ntheorem _root_.solution'
                self.assertEqual(solution.count(marker),1)
                self.assertTrue(solution.endswith('\nend '+namespace+'\n'))
                self.assertNotIn('\ntheorem solution',solution)
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
    def test_axiom_display_option_is_scoped_to_print_command(self):
        command=v.axiom_report_command('A.test')
        self.assertEqual(command,'set_option pp.universes false in\n#print axioms A.test\n')
        for invalid in ['A.test\nset_option pp.universes false','A.β','']:
            with self.assertRaises(ValueError):v.axiom_report_command(invalid)
    def test_exact_type_probe_bytes_and_detailed_options_are_preserved(self):
        probes=list((v.HERE/'fixtures/Probes').glob('*.lean.txt'))
        self.assertEqual(len(probes),20)
        for path in probes:
            original=path.read_text()
            self.assertIn('set_option pp.universes true',original)
            source=original+'\n'+v.axiom_report_command('solution')
            self.assertTrue(source.startswith(original+'\n'))
            self.assertEqual(source.count('set_option pp.universes false'),1)
    def test_axiom_allowlist_is_unchanged_and_unknown_axioms_are_reported(self):
        self.assertEqual(v.ALLOWED_AXIOMS,{'propext','Classical.choice','Quot.sound'})
        v.require_allowed_axioms(v.ALLOWED_AXIOMS,v.ALLOWED_AXIOMS,'definition')
        permitted=v.ALLOWED_AXIOMS|{'sorryAx'}
        v.require_allowed_axioms({'sorryAx'},permitted,'statement')
        for observed,allowed in [({'sorryAx'},v.ALLOWED_AXIOMS),({'customAxiom'},permitted),({'sorryAx.{u}'},permitted)]:
            output=io.StringIO()
            with contextlib.redirect_stdout(output),self.assertRaisesRegex(ValueError,'Unpermitted staged axiom'):
                v.require_allowed_axioms(observed,allowed,'A.test::statement')
            line=output.getvalue().strip()
            self.assertTrue(line.startswith('AXIOM_ALLOWLIST_FAILURE '))
            detail=json.loads(line.split(' ',1)[1])
            self.assertEqual(detail,{'context':'A.test::statement','observed':sorted(observed),'permitted':sorted(allowed),'unexpected':sorted(observed-allowed)})
    def test_axiom_parser_does_not_normalize_unexpected_names(self):
        self.assertEqual(v.axioms("'test' depends on axioms: [sorryAx.{u}]",'test'),{'sorryAx.{u}'})
    def test_kernel_bridge_uses_synchronous_kernel_and_solution_witness(self):
        source=v.kernel_type_bridge_source('Theorems.Target','Solutions.Target','Source.target')
        self.assertIn('kernelEnv.addDeclCore',source)
        self.assertIn('type := statement.type',source)
        self.assertIn('value := mkConst `solution (solution.levelParams.map Level.param)',source)
        self.assertIn('statement.levelParams == solution.levelParams',source)
        self.assertIn('kernelEnv.header.trustLevel == 0',source)
        self.assertIn('debug.skipKernelTC.get opts',source)
        self.assertIn('Kernel accepted altered-type negative control',source)
        self.assertIn('Kernel accepted altered-index negative control',source)
        for forbidden in ['addDeclWithoutChecking','Meta.isDefEq','sorryAx','axiomDecl']:
            self.assertNotIn(forbidden,source)
        with self.assertRaises(ValueError):v.kernel_type_bridge_source('A\nimport B','C','D')
    def test_kernel_bridge_requires_prior_exact_statement_match(self):
        prior=[{'node':'A.target','kind':'statement','comparison':'exact_text'}]
        v.require_exact_statement_for_bridge('solution','A.target',prior)
        for kind,name,records in [('statement','A.target',prior),('solution','B.target',prior),('solution','A.target',[]),
                                  ('solution','A.target',[{'node':'A.target','kind':'statement','comparison':'kernel_checked_type'}])]:
            with self.assertRaises(ValueError):v.require_exact_statement_for_bridge(kind,name,records)
    def test_kernel_bridge_record_preserves_both_unmodified_type_strings(self):
        row={'kind':'kernel_type_bridge','node':'A.target','status':'kernel_checked','trust_level':0,
             'controls':'positive_accepted_altered_type_and_index_rejected',
             'statement_type':'original._proof_1','solution_type':'solution._proof_1'}
        result=v.check_kernel_type_bridge_record(json.dumps(row),'A.target',row['statement_type'],row['solution_type'])
        self.assertNotEqual(result['original_type_sha256'],result['solution_type_sha256'])
        self.assertEqual(result['trust_level'],0)
        for key,value in [('node','B.target'),('status','unchecked'),('trust_level',1),('trust_level',False),
                          ('controls','not_run'),('statement_type','different'),('solution_type','different')]:
            with self.assertRaises(ValueError):v.check_kernel_type_bridge_record(json.dumps({**row,key:value}),'A.target',row['statement_type'],row['solution_type'])
        with self.assertRaises(ValueError):v.check_kernel_type_bridge_record(json.dumps(row)+'\n'+json.dumps(row),'A.target',row['statement_type'],row['solution_type'])
        with self.assertRaises(ValueError):v.check_kernel_type_bridge_record('{}','A.target',row['statement_type'],row['solution_type'])
        with self.assertRaises(ValueError):v.check_kernel_type_bridge_record(json.dumps({**row,'extra':True}),'A.target',row['statement_type'],row['solution_type'])

if __name__=='__main__':unittest.main()
