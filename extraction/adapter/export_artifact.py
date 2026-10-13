#!/usr/bin/env python3
"""Strict fresh-directory export for successful extraction facts. No upload action."""
import hashlib
import json
import os
from pathlib import Path
import stat

CAP=64*2**20
PER_FILE_CAP=16*2**20
TOP={'adapter_receipt.json','runtime.json','commands.json','decl_graph.jsonl','environment_facts.jsonl',
     'planner_graph.jsonl','original_types.jsonl','private_aliases.json','planner_manifest.json','phase_result.json','LICENSE'}
FACT_KINDS={'syntaxNode','binding','referenceIdentity','companionOptions'}


def digest(data):return hashlib.sha256(data).hexdigest()


def allowed_paths(modules):
    module_identities(modules)
    paths=set(TOP)
    for i,row in enumerate(modules):
        paths.update({f'sketch/{i:02d}.jsonl',f'planner_sketch/{i:02d}.jsonl',f'companion/{i:02d}.jsonl',
                      'sources/'+row['path']})
    return paths


def read_regular(path):
    if not stat.S_ISREG(Path(path).lstat().st_mode):raise ValueError('Export input is a link or special file')
    try:descriptor=os.open(path,os.O_RDONLY|getattr(os,'O_NOFOLLOW',0)|getattr(os,'O_NONBLOCK',0))
    except OSError as exc:raise ValueError('Export input cannot be opened safely') from exc
    with os.fdopen(descriptor,'rb') as stream:
        before=os.fstat(stream.fileno())
        if not stat.S_ISREG(before.st_mode) or before.st_nlink!=1 or before.st_size>PER_FILE_CAP:
            raise ValueError('Export input must be a single-link regular bounded file')
        data=stream.read(PER_FILE_CAP+1)
        after=os.fstat(stream.fileno())
        if len(data)>PER_FILE_CAP or (before.st_size,before.st_mtime_ns,before.st_ino)!=(after.st_size,after.st_mtime_ns,after.st_ino):
            raise ValueError('Export input changed during read')
    return data


def json_rows(data):
    return [json.loads(line) for line in data.decode().splitlines() if line.strip()]


def keys(row,required,label):
    if not isinstance(row,dict) or set(required)!=set(row):raise ValueError('Invalid or extra fields in '+label+' schema')


def safe_path(value):
    p=Path(value)
    if not isinstance(value,str) or p.is_absolute() or '..' in p.parts or str(p)!=value:
        raise ValueError('Noncanonical export-relative path')


def module_identities(modules):
    if not isinstance(modules,list) or len(modules)!=54:raise ValueError('Expected exactly 54 module provenance rows')
    names=set();paths=set();identities=set()
    for row in modules:
        keys(row,{'module','path','sha256'},'module provenance')
        name=row['module'];path=row['path'];sha=row['sha256']
        safe_path(path)
        if not isinstance(name,str) or not name.startswith('Erdos488.') or any(not part or part[0].isdigit() or any(not c.isascii() or not (c.isalnum() or c=='_') for c in part) for part in name.split('.')):
            raise ValueError('Invalid participating module identity')
        if path!=name.replace('.','/')+'.lean':raise ValueError('Module/path identity mismatch')
        if not isinstance(sha,str) or len(sha)!=64 or any(c not in '0123456789abcdef' for c in sha):raise ValueError('Invalid source provenance hash')
        if name in names or path in paths:raise ValueError('Duplicate participating module identity')
        names.add(name);paths.add(path);identities.add((name,path,sha))
    return identities


def no_runtime_paths(value):
    if isinstance(value,str) and any(x in value for x in ('/workspace/','/home/','/tmp/','/private/','/root/','/opt/','/usr/')):
        raise ValueError('Absolute runtime path leaked into metadata')
    if isinstance(value,dict):
        for k,v in value.items():no_runtime_paths(k);no_runtime_paths(v)
    elif isinstance(value,list):
        for v in value:no_runtime_paths(v)


def validate(path,data,modules):
    source_map={'sources/'+r['path']:r['sha256'] for r in modules}
    if path in source_map:
        if digest(data)!=source_map[path]:raise ValueError('Source snapshot hash mismatch')
        return
    if path=='LICENSE':
        if b'MIT License' not in data:raise ValueError('Expected public project MIT LICENSE')
        return
    if path.endswith('.jsonl'):
        rows=json_rows(data)
        if path in {'decl_graph.jsonl','planner_graph.jsonl'}:
            if not rows:raise ValueError('Empty declaration graph')
            for row in rows:
                keys(row,{'name','module','kind','isPrivate','isInstance','userName','startLine','endLine','typeDeps','valueDeps'} | ({'constructorNames','typePretty'} if path=='planner_graph.jsonl' else set()),'graph')
        elif path=='environment_facts.jsonl':
            if not rows:raise ValueError('Empty environment metadata')
            for row in rows:keys(row,{'name','module','userName','isPrivate','constructorNames','typePretty','kind'},'environment metadata')
        elif path=='original_types.jsonl':
            for row in rows:keys(row,{'name','module','typePretty'},'original type')
        elif path.startswith('companion/'):
            if not any(r.get('kind')=='companionOptions' and r.get('autoImplicit') is False for r in rows):
                raise ValueError('Missing strict-option companion receipt')
            for row in rows:
                if row.get('kind') not in FACT_KINDS:raise ValueError('Unexpected companion fact kind')
                if row['kind']=='syntaxNode':keys(row,{'kind','id','parent','region','syntaxKind','original','range','payload'},'syntax node')
                if row['kind']=='binding':keys(row,{'kind','region','syntaxNodeId','nameText','range'},'binding')
                if row['kind']=='companionOptions':keys(row,{'kind','module','autoImplicit'},'companion options')
                if row['kind']=='referenceIdentity':keys(row,{'kind','const','userName','originModule','start','end'},'reference identity')
        else:
            for row in rows:
                if row.get('kind')=='decl':keys(row,{'kind','nameText','declStart','declEnd','valStart','valKind','docstring','privateTok'},'declaration position')
                elif row.get('kind')=='ref':keys(row,{'kind','const','start','end'} | ({'userName','originModule'} if path.startswith('planner_sketch/') else set()),'reference position')
                else:raise ValueError('Unexpected official oracle fact kind')
        return
    obj=json.loads(data)
    no_runtime_paths(obj)
    if path=='phase_result.json':
        keys(obj,{'status','actual_node_generation','actual_transformed_type_comparison','platform_upload','provenance','started_utc','finished_utc','completed_modules','source_allowlist_unchanged','official_and_companion_reference_agreement'},'phase result')
        if (obj['status']!='EXTRACTION_PASSED_TRANSFORMS_NOT_RUN' or
            type(obj['completed_modules']) is not int or obj['completed_modules']!=54 or
            obj['source_allowlist_unchanged'] is not True or obj['official_and_companion_reference_agreement'] is not True or
            any(obj[field]!='NOT_RUN' for field in ('actual_node_generation','actual_transformed_type_comparison','platform_upload'))):
            raise ValueError('Only complete successful extraction with downstream stages not run can be exported')
    elif path=='planner_manifest.json':
        keys(obj,{'schema_version','graph_sha256','targets','modules','private_ref_aliases','provenance_kind','source_repository','source_base_commit','source_commit','compatibility_snapshot_id'},'planner manifest')
        expected=module_identities(modules)
        if not isinstance(obj['modules'],list) or len(obj['modules'])!=54:raise ValueError('Incomplete planner module coverage')
        planner_rows=[]
        for index,m in enumerate(obj['modules']):
            keys(m,{'module','source','source_sha256','sketch','sketch_sha256','companion','companion_sha256','reference_filter'},'planner module')
            for name in ('source','sketch','companion'):safe_path(m[name])
            peer=modules[index]
            if (m['module']!=peer['module'] or m['source']!='sources/'+peer['path'] or m['source_sha256']!=peer['sha256'] or
                m['sketch']!=f'planner_sketch/{index:02d}.jsonl' or m['companion']!=f'companion/{index:02d}.jsonl' or m['reference_filter'] is not None):
                raise ValueError('Planner module/source/oracle binding mismatch')
            planner_rows.append({'module':m['module'],'path':m['source'][len('sources/'):],'sha256':m['source_sha256']})
        if module_identities(planner_rows)!=expected:raise ValueError('Planner/source module identities disagree')
    elif path=='adapter_receipt.json':
        keys(obj,{'schema_version','status','target','source_repository','source_base_commit','source_manifest_sha256','modules','project_config_sha256','project_license_sha256','upstream_commit','official_tools','tools_sha256','companions','official_stage2_options','execution_status','artifact_cap_mib','provenance'},'adapter receipt')
        if module_identities(obj['modules'])!=module_identities(modules):raise ValueError('Source provenance identities disagree')
        if (obj['status']!='EXECUTED_WITH_SUCCESSFUL_FACT_AGREEMENT' or
            obj['execution_status']!='All 110 Lean commands and official/companion reference comparisons passed' or
            not isinstance(obj['companions'],dict) or obj['companions'].get('Lean_compilation')!='PASSED_IN_THIS_RUNTIME'):
            raise ValueError('Only executed adapter receipts with compiled companions can be exported')
    elif path=='runtime.json':
        if not isinstance(obj,dict) or set(obj)!={'lean_version','dependency_revisions','search_path_capture','source_tree_sha256'}:
            raise ValueError('Unexpected runtime metadata fields')
    elif path=='commands.json':
        if not isinstance(obj,list) or len(obj)!=110:raise ValueError('Expected two environment plus 108 per-source commands')
        expected_steps=['stage1','environment']+[s for i in range(54) for s in (f'oracle-{i:02d}',f'companion-{i:02d}')]
        if [c.get('step') for c in obj]!=expected_steps:raise ValueError('Unexpected command coverage/order')
        for cmd in obj:
            if set(cmd)!={'step','argv_placeholders','cwd_placeholder','exit_code','seconds','stdout_sha256','stderr_sha256'} or cmd['exit_code']!=0:
                raise ValueError('Unexpected command receipt')
            if cmd['cwd_placeholder']!='<output>/work' or any(not isinstance(x,str) or x.startswith('/') for x in cmd['argv_placeholders']):raise ValueError('Absolute command path or invalid cwd')
    elif path=='private_aliases.json':
        if not isinstance(obj,list):raise ValueError('Expected private alias array')
        for alias in obj:
            if set(alias)!={'const','userName','module'}:raise ValueError('Unexpected alias fields')


def export(source,staging,modules,expected_license_hash,cap=CAP):
    source,staging=Path(source),Path(staging)
    if cap>CAP or cap<=0:raise ValueError('Export cap cannot exceed approved 64 MiB ceiling')
    if staging.exists() or staging.is_symlink():raise ValueError('Export destination must be new')
    if source.is_symlink() or not source.is_dir():raise ValueError('Invalid receipt source directory')
    allowed=allowed_paths(modules)
    expected_dirs={str(parent) for p in allowed for parent in Path(p).parents if str(parent)!='.'}
    actual=set()
    for directory,dirs,files in os.walk(source,followlinks=False):
        for name in dirs:
            p=Path(directory)/name; rel=str(p.relative_to(source)); mode=p.lstat().st_mode
            if not stat.S_ISDIR(mode) or rel not in expected_dirs:raise ValueError('Unexpected/link/special export directory')
        for name in files:
            p=Path(directory)/name;rel=str(p.relative_to(source))
            if rel not in allowed:raise ValueError('Unexpected export file: '+rel)
            actual.add(rel)
    if actual!=allowed:raise ValueError('Export file set is incomplete')
    blobs={};total=0
    for rel in sorted(allowed):
        data=read_regular(source/rel);total+=len(data)
        if total>cap:raise ValueError('Uncompressed export exceeds 64 MiB cap')
        validate(rel,data,modules);blobs[rel]=data
    if digest(blobs['LICENSE'])!=expected_license_hash:raise ValueError('Project MIT LICENSE hash changed')
    planner=json.loads(blobs['planner_manifest.json'])
    if digest(blobs['planner_graph.jsonl'])!=planner['graph_sha256']:raise ValueError('Planner graph hash mismatch')
    for module in planner['modules']:
        if digest(blobs[module['source']])!=module['source_sha256'] or digest(blobs[module['sketch']])!=module['sketch_sha256'] or digest(blobs[module['companion']])!=module['companion_sha256']:
            raise ValueError('Planner source/oracle hash mismatch')
    inventory={'schema_version':1,'status':'VALIDATED_RELATIVE_PATH_EXPORT','upload_performed':False,
               'cap_bytes':cap,'files':[{'path':k,'bytes':len(v),'sha256':digest(v)} for k,v in blobs.items()]}
    inventory_data=(json.dumps(inventory,indent=2)+'\n').encode()
    if total+len(inventory_data)>cap:raise ValueError('Final inventory would exceed export cap')
    staging.mkdir(parents=True)
    for rel,data in [*blobs.items(),('EXPORT_MANIFEST.json',inventory_data)]:
        destination=staging/rel;destination.parent.mkdir(parents=True,exist_ok=True)
        with destination.open('xb') as stream:stream.write(data)
        if digest(read_regular(destination))!=digest(data):raise ValueError('Fresh export copy failed verification')
    return validate_artifact(staging)


def validate_artifact(path):
    """Revalidate exact file inventory, schemas, hashes and caps immediately before upload."""
    root=Path(path)
    if root.is_symlink() or not root.is_dir():raise ValueError('Artifact root must be a regular directory')
    inventory_data=read_regular(root/'EXPORT_MANIFEST.json')
    inventory=json.loads(inventory_data)
    keys(inventory,{'schema_version','status','upload_performed','cap_bytes','files'},'export inventory')
    if inventory['schema_version']!=1 or inventory['status']!='VALIDATED_RELATIVE_PATH_EXPORT' or inventory['upload_performed'] is not False or type(inventory['cap_bytes']) is not int or not 0<inventory['cap_bytes']<=CAP:
        raise ValueError('Invalid export inventory status/cap')
    config=json.loads(read_regular(root/'adapter_receipt.json'))
    modules=config['modules'];expected=allowed_paths(modules)
    recorded={}
    for row in inventory['files']:
        keys(row,{'path','bytes','sha256'},'inventory file')
        safe_path(row['path'])
        if row['path'] in recorded:raise ValueError('Duplicate inventory path')
        recorded[row['path']]=row
    if set(recorded)!=expected:raise ValueError('Inventory is not the exact expected file set')
    actual=set();directories={str(parent) for p in expected for parent in Path(p).parents if str(parent)!='.'}
    for directory,dirs,files in os.walk(root,followlinks=False):
        for name in dirs:
            child=Path(directory)/name
            if not stat.S_ISDIR(child.lstat().st_mode) or str(child.relative_to(root)) not in directories:raise ValueError('Unexpected/link/special artifact directory')
        for name in files:actual.add(str((Path(directory)/name).relative_to(root)))
    if actual!=expected|{'EXPORT_MANIFEST.json'}:raise ValueError('Unexpected or missing artifact path')
    total=len(inventory_data);blobs={}
    for relative,entry in recorded.items():
        data=read_regular(root/relative)
        if type(entry['bytes']) is not int or len(data)!=entry['bytes'] or digest(data)!=entry['sha256']:raise ValueError('Artifact hash/size mismatch')
        total+=len(data)
        if total>inventory['cap_bytes']:raise ValueError('Artifact exceeds approved cap')
        validate(relative,data,modules);blobs[relative]=data
    if digest(blobs['LICENSE'])!=config['project_license_sha256']:raise ValueError('MIT LICENSE hash mismatch')
    planner=json.loads(blobs['planner_manifest.json'])
    if digest(blobs['planner_graph.jsonl'])!=planner['graph_sha256']:raise ValueError('Planner graph drift')
    for module in planner['modules']:
        if any(digest(blobs[module[p]])!=module[h] for p,h in [('source','source_sha256'),('sketch','sketch_sha256'),('companion','companion_sha256')]):raise ValueError('Planner input hash drift')
    for p in (config['provenance'],json.loads(blobs['phase_result.json'])['provenance']):
        keys(p,{'repository','wrapper_commit','harness_commit','workflow_run_url'},'run provenance')
        prefix='https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/'
        if p['repository']!='jjtripodo-lgtm/erdos-670-verification' or p['harness_commit']!='5510ffd94156d48dbe393ac619586b935212da79' or len(p['wrapper_commit'])!=40 or any(c not in '0123456789abcdef' for c in p['wrapper_commit']) or not p['workflow_run_url'].startswith(prefix) or not p['workflow_run_url'][len(prefix):].isdigit():raise ValueError('Invalid immutable-code/run provenance')
    if config['provenance']!=json.loads(blobs['phase_result.json'])['provenance']:raise ValueError('Run provenance disagreement')
    return {'file_count':len(actual),'uncompressed_bytes':total,'cap_bytes':inventory['cap_bytes']}


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description='Strictly revalidate a completed relative-path artifact; no upload')
    parser.add_argument('path',type=Path)
    args=parser.parse_args()
    print(json.dumps(validate_artifact(args.path),sort_keys=True))
