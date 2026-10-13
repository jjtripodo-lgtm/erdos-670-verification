"""Synthetic adapter/strict-export tests only. Never starts Lean, Lake or GitHub work."""
import contextlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from prepare_adapter import prepare as real_prepare,digest,replace_once,EXTRACTOR_HASHES
from compare_type_dumps import compare,load
from make_type_probe import render
from run_extraction import main,merge_oracles,capture_search_paths,provenance,FROZEN_HARNESS,failure_capsule
from export_artifact import export,validate,validate_artifact,CAP,PER_FILE_CAP

HERE=Path(__file__).resolve().parent
REFS=Path(os.environ.get('PROVE2ME_TEST_EXTRACTORS',str(HERE.parent/'reference')))
SYNTHETIC_CONFIG={
 'lean-toolchain':b'leanprover/lean4:v4.33.1\n',
 'lakefile.toml':b'name="synthetic"\n[leanOptions]\nautoImplicit=false\n[[require]]\nname="mathlib"\nrev="0df444a360eaa60ab8c11dca51a86af692955474"\n',
 'lake-manifest.json':b'{"packages":[{"name":"mathlib","rev":"0df444a360eaa60ab8c11dca51a86af692955474"}]}\n',
 'LICENSE':b'MIT License\nSynthetic test fixture only.\n'}

def prepare(*args):
    # Isolate synthetic fixture hashes in this test process only; production pins stay fixed.
    with patch.dict('prepare_adapter.CONFIG_HASHES',{k:digest(v) for k,v in SYNTHETIC_CONFIG.items()},clear=True):
        return real_prepare(*args)



def fixture(root):
    project=root/'candidate';project.mkdir();(project/'Erdos488').mkdir();rows=[]
    for i in range(54):
        rel=f'Erdos488/M{i}.lean';data=f'-- SYNTHETIC module {i}; not compiled\n'.encode()
        (project/rel).write_bytes(data)
        rows.append({'module':f'Erdos488.M{i}','path':rel,'prove2me_sha256':digest(data)})
    (project/'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
    (project/'lakefile.toml').write_text('name="synthetic"\n[leanOptions]\nautoImplicit=false\n[[require]]\nname="mathlib"\nrev="0df444a360eaa60ab8c11dca51a86af692955474"\n')
    (project/'lake-manifest.json').write_text('{"packages":[{"name":"mathlib","rev":"0df444a360eaa60ab8c11dca51a86af692955474"}]}\n')
    (project/'LICENSE').write_text('MIT License\nSynthetic test fixture only.\n')
    manifest=root/'SOURCE_MANIFEST.json';manifest.write_text(json.dumps({'module_count':54,'source_commit':'synthetic','source_repository':'synthetic','modules':rows}))
    return project,manifest


def receipt_fixture(root):
    project,manifest=fixture(root);config=prepare(project,manifest,root/'out',REFS)
    receipts=root/'out/receipts'
    prov={'repository':'jjtripodo-lgtm/erdos-670-verification','wrapper_commit':'a'*40,'harness_commit':FROZEN_HARNESS,'workflow_run_url':'https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/1'}
    config['provenance']=prov
    # Synthetic success receipt shape only; this fixture never executes Lean.
    config['status']='EXECUTED_WITH_SUCCESSFUL_FACT_AGREEMENT'
    config['execution_status']='All 110 Lean commands and official/companion reference comparisons passed'
    config['companions']['Lean_compilation']='PASSED_IN_THIS_RUNTIME'
    def put(rel,data):
        p=receipts/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    def js(rel,obj,lines=False):
        put(rel,((('\n'.join(json.dumps(r) for r in obj)) if lines else json.dumps(obj))+'\n').encode())
    js('adapter_receipt.json',config)
    js('runtime.json',{'lean_version':'Synthetic 4.33.1','dependency_revisions':{},'search_path_capture':'synthetic','source_tree_sha256':'0'*64})
    steps=['stage1','environment']+[s for i in range(54) for s in (f'oracle-{i:02d}',f'companion-{i:02d}')]
    js('commands.json',[{'step':s,'argv_placeholders':['<toolchain-bin>/lean'],'cwd_placeholder':'<output>/work','exit_code':0,'seconds':0,'stdout_sha256':'0'*64,'stderr_sha256':'0'*64} for s in steps])
    g={'name':'Erdos488.M0.synthetic','userName':'Erdos488.M0.synthetic','module':'Erdos488.M0','kind':'theorem','isPrivate':False,'isInstance':False,'startLine':1,'endLine':1,'typeDeps':[],'valueDeps':[]}
    js('decl_graph.jsonl',[g],True)
    js('planner_graph.jsonl',[{**g,'constructorNames':[],'typePretty':'True'}],True)
    js('environment_facts.jsonl',[{'name':g['name'],'userName':g['name'],'module':g['module'],'kind':'environmentDeclaration','isPrivate':False,'constructorNames':[],'typePretty':'True'}],True)
    js('original_types.jsonl',[{'name':g['name'],'module':g['module'],'typePretty':'True'}],True)
    modules=[]
    for i,row in enumerate(config['modules']):
        put('sources/'+row['path'],(project/row['path']).read_bytes())
        js(f'sketch/{i:02d}.jsonl',[],True);js(f'planner_sketch/{i:02d}.jsonl',[],True)
        js(f'companion/{i:02d}.jsonl',[{'kind':'companionOptions','module':row['module'],'autoImplicit':False}],True)
        modules.append({'module':row['module'],'source':'sources/'+row['path'],'source_sha256':row['sha256'],
                        'sketch':f'planner_sketch/{i:02d}.jsonl','sketch_sha256':digest((receipts/f'planner_sketch/{i:02d}.jsonl').read_bytes()),
                        'companion':f'companion/{i:02d}.jsonl','companion_sha256':digest((receipts/f'companion/{i:02d}.jsonl').read_bytes()),'reference_filter':None})
    js('private_aliases.json',[])
    js('planner_manifest.json',{'schema_version':1,'graph_sha256':digest((receipts/'planner_graph.jsonl').read_bytes()),'targets':[g['name']],'modules':modules,'private_ref_aliases':[],
                              'provenance_kind':'synthetic','source_repository':'synthetic','source_base_commit':'synthetic','source_commit':None,'compatibility_snapshot_id':'0'*64})
    js('phase_result.json',{'status':'EXTRACTION_PASSED_TRANSFORMS_NOT_RUN','actual_node_generation':'NOT_RUN','actual_transformed_type_comparison':'NOT_RUN','platform_upload':'NOT_RUN',
                           'provenance':prov,'started_utc':'synthetic','finished_utc':'synthetic','completed_modules':54,'source_allowlist_unchanged':True,'official_and_companion_reference_agreement':True})
    put('LICENSE',(project/'LICENSE').read_bytes())
    return config,receipts


class AdapterTests(unittest.TestCase):
    def test_preparation_is_inert_and_official_tools_respect_edit_scope(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);project,manifest=fixture(root)
            before={str(p):p.read_bytes() for p in project.rglob('*') if p.is_file()}
            with patch('subprocess.Popen',side_effect=AssertionError('must not launch')):
                config=prepare(project,manifest,root/'out',REFS)
            self.assertEqual(before,{str(p):p.read_bytes() for p in project.rglob('*') if p.is_file()})
            self.assertEqual(config['status'],'PREPARED_NOT_EXECUTED')
            self.assertNotIn(str(root),json.dumps(config))
            self.assertEqual((root/'out/tools/extract_sketch_info.lean').read_bytes(),(REFS/'extract_sketch_info.lean').read_bytes())
            expected=(REFS/'extract_decl_graph.lean').read_text().replace('import SumSquares\n',''.join(f'import Erdos488.M{i}\n' for i in range(54))).replace('let projPrefix := `SumSquares','let projPrefix := `Erdos488')
            self.assertEqual((root/'out/tools/extract_decl_graph.lean').read_text(),expected)
            self.assertIn('autoImplicit false',(root/'out/tools/source_facts.lean').read_text())
            self.assertEqual(config['companions']['Lean_compilation'],'NOT_RUN')

    def test_preparation_inside_candidate_rejected(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);project,manifest=fixture(root)
            with self.assertRaises(ValueError):prepare(project,manifest,project/'bad',REFS)

    def test_source_hash_drift_rejected(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);project,manifest=fixture(root);(project/'Erdos488/M0.lean').write_text('-- changed')
            with self.assertRaises(ValueError):prepare(project,manifest,root/'out',REFS)

    def test_extra_source_rejected_but_axiom_audit_outside_manifest_is_not_extracted(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);project,manifest=fixture(root);(project/'AxiomAudit.lean').write_text('-- synthetic audit')
            result=prepare(project,manifest,root/'out',REFS);self.assertEqual(len(result['modules']),54)
            (project/'Erdos488/Extra.lean').write_text('-- extra')
            with self.assertRaises(ValueError):prepare(project,manifest,root/'bad',REFS)

    def test_options_or_mathlib_drift_rejected(self):
        for filename,data in [('lakefile.toml','name="synthetic"\n'),('lake-manifest.json','{"packages":[]}')]:
            with tempfile.TemporaryDirectory(dir=HERE) as tmp:
                root=Path(tmp);project,manifest=fixture(root);(project/filename).write_text(data)
                with self.assertRaises(ValueError):prepare(project,manifest,root/'out',REFS)

    def test_tool_hash_and_patch_count_checks_are_explicit(self):
        with self.assertRaises(ValueError):replace_once('foo foo','foo','bar')
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);project,manifest=fixture(root);refs=root/'refs';refs.mkdir();(refs/'extract_decl_graph.lean').write_text('-- wrong')
            with self.assertRaises(ValueError):prepare(project,manifest,root/'out',refs)

    def test_execution_flags_required_before_runtime(self):
        argv=['--'+flag for flag in []]
        for flag in ('project','manifest','output','toolchain-bin','extractors','wrapper-commit','harness-commit','workflow-run-url'):argv+=['--'+flag,'unused']
        with patch('run_extraction.preflight_runtime',side_effect=AssertionError('must not execute')):
            with self.assertRaises(SystemExit) as caught,contextlib.redirect_stderr(io.StringIO()):main(argv)
            self.assertEqual(caught.exception.code,2)

    def test_relative_lean_paths_are_absolutized_before_cwd_change(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);project,manifest=fixture(root)
            data={'LEAN_PATH':'.lake/build/lib/lean:deps/lib','LEAN_SRC_PATH':'.','LEAN_DYN_LIB_PATH':None,'LD_LIBRARY_PATH':None,'DYLD_LIBRARY_PATH':None}
            with patch('subprocess.check_output',return_value=json.dumps(data).encode()):
                env=capture_search_paths(project,root/'bin',{})
            self.assertEqual(env['LEAN_PATH'].split(os.pathsep)[0],str(project/'.lake/build/lib/lean'))
            self.assertEqual(env['LEAN_SRC_PATH'],str(project))

    def test_official_companion_disagreement_blocks(self):
        p={'line':1,'col':0,'offset':0};q={'line':1,'col':1,'offset':1}
        old=[{'kind':'ref','const':'P.x','start':p,'end':q}]
        extra=[{'kind':'companionOptions','module':'P','autoImplicit':False},{'kind':'referenceIdentity','const':'P.x','userName':'P.x','originModule':'P','start':p,'end':q}]
        self.assertEqual(merge_oracles(old,extra,'P')[0]['originModule'],'P')
        extra[-1]['const']='P.y'
        with self.assertRaises(ValueError):merge_oracles(old,extra,'P')

    def test_provenance_is_canonical_and_frozen(self):
        with patch.dict(os.environ,{},clear=True):
            self.assertEqual(provenance('a'*40,FROZEN_HARNESS,'https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/1')['harness_commit'],FROZEN_HARNESS)
            with self.assertRaises(ValueError):provenance('a'*40,'b'*40,'https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/1')

    def test_failure_capsule_is_bounded_and_never_echoes_upstream(self):
        project=Path('/workspace/private/candidate');tools=Path('/workspace/private/tools')
        own=(str(tools/'source_facts.lean')+":12:3: error: unknown field at /workspace/private/secret\n  private source excerpt must not appear\n").encode()
        capsule=json.loads(failure_capsule('companion-00',1,None,b'',own,project,tools,[]))
        self.assertEqual(capsule['headers'][0]['file'],'companions/source_facts.lean.txt')
        self.assertNotIn('/workspace/',json.dumps(capsule))
        self.assertNotIn('source excerpt',json.dumps(capsule))
        upstream=json.loads(failure_capsule('oracle-00',1,None,b'',own,project,tools,[]))
        self.assertEqual(upstream['headers'],[])
        self.assertLessEqual(len(failure_capsule('companion-00',1,None,b'',own*10000,project,tools,[]).encode()),8192)

    def test_exact_type_gate_never_guesses_away_differences(self):
        result=compare({'a':'Nat'},{'b':'Nat'},[{'original':'a','staged':'b'}]);self.assertEqual(result['status'],'EXACT_TYPE_TEXT_EQUAL');self.assertFalse(result['upload_ready'])
        self.assertEqual(compare({'a':'Sort u_1'},{'b':'Sort u_2'},[{'original':'a','staged':'b'}])['status'],'BLOCKED_TYPE_TEXT_DIFF')
        with self.assertRaises(ValueError):compare({}, {}, [])

    def test_probe_accepts_only_public_conservative_names(self):
        self.assertIn('import Solutions.Sol_Target',render('Solutions.Sol_Target','solution','key'))
        with self.assertRaises(ValueError):render('M\nimport X','solution','key')
        with self.assertRaises(ValueError):render('M','_private.X.7.x','key')


class ExportTests(unittest.TestCase):
    def test_success_semantics_fail_closed_on_initial_export(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);cfg,r=receipt_fixture(root)
            cases=[('phase_result.json','completed_modules',53),('phase_result.json','completed_modules',54.0),
                   ('phase_result.json','source_allowlist_unchanged',False),('phase_result.json','source_allowlist_unchanged',1),
                   ('phase_result.json','official_and_companion_reference_agreement',False),
                   ('phase_result.json','actual_node_generation','PASSED'),('phase_result.json','actual_transformed_type_comparison','PASSED'),
                   ('phase_result.json','platform_upload','PASSED'),('adapter_receipt.json','status','PREPARED_NOT_EXECUTED'),
                   ('adapter_receipt.json','execution_status','No Lean process was launched by preparation')]
            for filename,field,value in cases:
                with self.subTest(filename=filename,field=field,value=value):
                    path=r/filename;original=path.read_bytes();obj=json.loads(original);obj[field]=value;path.write_text(json.dumps(obj))
                    with self.assertRaises(ValueError):export(r,root/'artifact',cfg['modules'],cfg['project_license_sha256'])
                    self.assertFalse((root/'artifact').exists());path.write_bytes(original)
            path=r/'adapter_receipt.json';obj=json.loads(path.read_text());obj['companions']['Lean_compilation']='NOT_RUN';path.write_text(json.dumps(obj))
            with self.assertRaises(ValueError):export(r,root/'artifact',cfg['modules'],cfg['project_license_sha256'])

    def test_success_semantics_rechecked_after_inventory_rehash(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);cfg,r=receipt_fixture(root);artifact=root/'artifact'
            export(r,artifact,cfg['modules'],cfg['project_license_sha256'])
            for filename,field,value in [('phase_result.json','source_allowlist_unchanged',False),('adapter_receipt.json','status','PREPARED_NOT_EXECUTED')]:
                with self.subTest(filename=filename):
                    path=artifact/filename;original=path.read_bytes();obj=json.loads(original);obj[field]=value;data=json.dumps(obj).encode();path.write_bytes(data)
                    inventory_path=artifact/'EXPORT_MANIFEST.json';original_inventory=inventory_path.read_bytes();inventory=json.loads(original_inventory)
                    for row in inventory['files']:
                        if row['path']==filename:row.update(bytes=len(data),sha256=digest(data))
                    inventory_path.write_text(json.dumps(inventory))
                    with self.assertRaises(ValueError):validate_artifact(artifact)
                    path.write_bytes(original);inventory_path.write_bytes(original_inventory)

    def test_module_identity_coverage_and_binding_rejected(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);cfg,r=receipt_fixture(root)
            for filename in ('adapter_receipt.json','planner_manifest.json'):
                original=(r/filename).read_bytes()
                for change in ('duplicate','renamed','path_swap','hash_swap','oracle_swap'):
                    with self.subTest(filename=filename,change=change):
                        obj=json.loads(original);rows=obj['modules'];field='path' if filename=='adapter_receipt.json' else 'source'
                        if change=='duplicate':rows[1]=dict(rows[0])
                        elif change=='renamed':rows[0]['module']='Erdos488.Renamed'
                        elif change=='path_swap':rows[0][field],rows[1][field]=rows[1][field],rows[0][field]
                        elif change=='hash_swap':
                            key='sha256' if filename=='adapter_receipt.json' else 'source_sha256'
                            rows[0][key],rows[1][key]=rows[1][key],rows[0][key]
                        elif filename=='planner_manifest.json':rows[0]['companion'],rows[1]['companion']=rows[1]['companion'],rows[0]['companion']
                        else:continue
                        with self.assertRaises(ValueError):validate(filename,json.dumps(obj).encode(),cfg['modules'])
            duplicated=[dict(row) for row in cfg['modules']];duplicated[1]=dict(duplicated[0])
            with self.assertRaises(ValueError):export(r,root/'artifact',duplicated,cfg['project_license_sha256'])

    def test_fresh_export_and_revalidation(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);cfg,receipts=receipt_fixture(root)
            result=export(receipts,root/'artifact',cfg['modules'],cfg['project_license_sha256'])
            self.assertEqual(result,validate_artifact(root/'artifact'));self.assertLess(result['uncompressed_bytes'],CAP)
            self.assertTrue((root/'artifact/LICENSE').is_file())
            self.assertFalse((root/'artifact/tools').exists())

    def test_unexpected_file_or_directory_rejected(self):
        for kind in ('file','dir'):
            with tempfile.TemporaryDirectory(dir=HERE) as tmp:
                root=Path(tmp);cfg,r=receipt_fixture(root)
                if kind=='file':(r/'unexpected.json').write_text('{}')
                else:(r/'unexpected').mkdir()
                with self.assertRaises(ValueError):export(r,root/'artifact',cfg['modules'],cfg['project_license_sha256'])

    def test_symlink_hardlink_and_fifo_rejected(self):
        for kind in ('symlink','hardlink','fifo'):
            with tempfile.TemporaryDirectory(dir=HERE) as tmp:
                root=Path(tmp);cfg,r=receipt_fixture(root);target=r/'runtime.json';data=target.read_bytes();target.unlink();outside=root/'outside';outside.write_bytes(data)
                if kind=='symlink':target.symlink_to(outside)
                elif kind=='hardlink':os.link(outside,target)
                else:os.mkfifo(target)
                with self.assertRaises(ValueError):export(r,root/'artifact',cfg['modules'],cfg['project_license_sha256'])

    def test_mutated_artifact_and_extra_schema_fields_rejected(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);cfg,r=receipt_fixture(root);export(r,root/'artifact',cfg['modules'],cfg['project_license_sha256'])
            (root/'artifact/LICENSE').write_text('MIT License\nchanged')
            with self.assertRaises(ValueError):validate_artifact(root/'artifact')
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);cfg,r=receipt_fixture(root);p=r/'decl_graph.jsonl';g=json.loads(p.read_text());g['unapproved_extra']='secret';p.write_text(json.dumps(g)+'\n')
            with self.assertRaises(ValueError):export(r,root/'artifact',cfg['modules'],cfg['project_license_sha256'])

    def test_runtime_paths_and_caps_rejected(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);cfg,r=receipt_fixture(root);p=r/'runtime.json';obj=json.loads(p.read_text());obj['search_path_capture']='/workspace/private';p.write_text(json.dumps(obj))
            with self.assertRaises(ValueError):export(r,root/'artifact',cfg['modules'],cfg['project_license_sha256'])
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);cfg,r=receipt_fixture(root)
            with self.assertRaises(ValueError):export(r,root/'artifact',cfg['modules'],cfg['project_license_sha256'],cap=100)
            with self.assertRaises(ValueError):export(r,root/'artifact',cfg['modules'],cfg['project_license_sha256'],cap=CAP+1)


if __name__=='__main__':unittest.main()
