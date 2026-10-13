#!/usr/bin/env python3
"""Private serial extraction using unchanged official oracle plus independent companions."""
from __future__ import annotations
import argparse
from bisect import bisect_right
from datetime import datetime,timezone
import json
import os
from pathlib import Path
import resource
import re
import shutil
import signal
import stat
import subprocess
import sys
import time
from prepare_adapter import prepare,digest
from export_artifact import export,validate,CAP,PER_FILE_CAP

FROZEN_HARNESS='5510ffd94156d48dbe393ac619586b935212da79'
REPOSITORY='jjtripodo-lgtm/erdos-670-verification'


def provenance(wrapper,harness,url):
    if len(wrapper)!=40 or any(c not in '0123456789abcdef' for c in wrapper):raise ValueError('Invalid wrapper commit')
    if harness!=FROZEN_HARNESS:raise ValueError('Harness commit must equal frozen reviewed SHA')
    prefix=f'https://github.com/{REPOSITORY}/actions/runs/'
    if not url.startswith(prefix) or not url[len(prefix):].isdigit():raise ValueError('Invalid canonical workflow run URL')
    if os.environ.get('GITHUB_SHA') and os.environ['GITHUB_SHA']!=wrapper:raise ValueError('Wrapper commit differs from running workflow')
    if os.environ.get('GITHUB_REPOSITORY') and os.environ['GITHUB_REPOSITORY']!=REPOSITORY:raise ValueError('Wrong workflow repository')
    if os.environ.get('GITHUB_RUN_ID') and os.environ['GITHUB_RUN_ID']!=url[len(prefix):]:raise ValueError('Workflow run ID mismatch')
    return {'repository':REPOSITORY,'wrapper_commit':wrapper,'harness_commit':harness,'workflow_run_url':url}


def snapshot(project):
    found={}
    for directory,dirs,files in os.walk(project,followlinks=False):
        if Path(directory)==project:dirs[:]=[d for d in dirs if d not in {'.lake','.git'}]
        for name in dirs:
            if not stat.S_ISDIR((Path(directory)/name).lstat().st_mode):raise ValueError('Candidate directory link/special file')
        for name in files:
            p=Path(directory)/name
            if not stat.S_ISREG(p.lstat().st_mode):raise ValueError('Candidate contains link/special file')
            found[str(p.relative_to(project))]=digest(p.read_bytes())
    return found


def preflight_runtime(project,toolbin,rows):
    for name in ('lean','lake'):
        binary=toolbin/name
        if not binary.is_file() or binary.resolve().name=='elan':raise ValueError('Native pinned binaries required')
    version=subprocess.check_output([str(toolbin/'lean'),'--version'],text=True,timeout=20).strip()
    if 'version 4.33.1,' not in version and 'version 4.33.1 ' not in version:raise ValueError('Lean version is not 4.33.1')
    for row in rows:
        if not (project/'.lake/build/lib/lean'/Path(row['path']).with_suffix('.olean')).is_file():
            raise ValueError('Existing source objects required; adapter will not rebuild')
    deps={}
    for dep in json.loads((project/'lake-manifest.json').read_text())['packages']:
        folder=project/'.lake/packages'/dep['name']
        if not folder.is_dir() or folder.is_symlink():raise ValueError('Missing independent pinned dependency checkout')
        rev=subprocess.check_output(['git','-C',str(folder),'rev-parse','HEAD'],text=True,timeout=20).strip()
        dirty=subprocess.check_output(['git','-C',str(folder),'status','--porcelain','--untracked-files=all'],text=True,timeout=20).strip()
        if rev!=dep['rev'] or dirty:raise ValueError('Dependency revision/cleanliness mismatch')
        deps[dep['name']]=rev
    return {'lean_version':version,'dependency_revisions':deps}


def capture_search_paths(project,toolbin,env):
    names=['LEAN_PATH','LEAN_SRC_PATH','LEAN_DYN_LIB_PATH','LD_LIBRARY_PATH','DYLD_LIBRARY_PATH']
    program='import os,json; print(json.dumps({k:os.environ.get(k) for k in '+repr(names)+'}))'
    raw=subprocess.check_output([str(toolbin/'lake'),'--no-cache','env',sys.executable,'-c',program],cwd=project,env=env,timeout=60)
    selected=json.loads(raw)
    if set(selected)!=set(names):raise ValueError('Unexpected search-path environment fields')
    for key,value in selected.items():
        if value is None:
            env.pop(key,None);continue
        if not isinstance(value,str):raise ValueError('Invalid search-path value')
        paths=[]
        for entry in value.split(os.pathsep):
            path=Path(entry) if entry else project
            paths.append(str((project/path).resolve() if not path.is_absolute() else path.resolve()))
        env[key]=os.pathsep.join(paths)
    built=str((project/'.lake/build/lib/lean').resolve())
    if built not in env.get('LEAN_PATH','').split(os.pathsep):raise ValueError('Captured Lean path omits project objects')
    return env


def read_jsonl(path):
    rows=[]
    for line in path.read_text().splitlines():
        if line.strip():
            value=json.loads(line)
            if not isinstance(value,dict):raise ValueError('Non-object oracle output')
            rows.append(value)
    return rows


def check_positions(rows,source):
    starts=[0]+[i+1 for i,b in enumerate(source) if b==10]
    def point(p):
        if not isinstance(p,dict) or set(p)!={'line','col','offset'} or any(type(p[k]) is not int for k in p):raise ValueError('Invalid source position')
        off=p['offset']
        if not 0<=off<=len(source) or p['line']!=bisect_right(starts,off) or p['col']<0:raise ValueError('Source position out of bounds')
        if off<len(source) and source[off]&0xC0==0x80:raise ValueError('Source position splits UTF-8')
    def walk(value):
        if isinstance(value,dict):
            if set(value)=={'line','col','offset'}:point(value)
            else:
                for child in value.values():walk(child)
        elif isinstance(value,list):
            for child in value:walk(child)
    walk(rows)


def merge_oracles(official,companion,module):
    options=[r for r in companion if r.get('kind')=='companionOptions']
    if len(options)!=1 or options[0].get('autoImplicit') is not False or options[0].get('module')!=module:
        raise ValueError('Missing strict-option source companion receipt')
    def key(row):return (row['const'],row['start']['offset'],row['end']['offset'])
    refs={}
    for row in companion:
        if row.get('kind')=='referenceIdentity':
            k=key(row)
            if k in refs and refs[k]!=row:raise ValueError('Ambiguous companion reference identity')
            refs[k]=row
    official_keys={key(row) for row in official if row.get('kind')=='ref'}
    if official_keys!=set(refs):raise ValueError('Official/default-option and strict-option reference ranges or identities disagree')
    merged=[]
    for row in official:
        if row.get('kind') not in {'decl','ref'}:raise ValueError('Unexpected official Stage 2 output')
        copy=dict(row)
        if row['kind']=='ref':
            peer=refs[key(row)];copy.update(userName=peer['userName'],originModule=peer['originModule'])
        merged.append(copy)
    return merged


def failure_capsule(step,exit_code,guard,stdout,stderr,project,tools,rows):
    """Bounded job-log diagnostics; never include raw logs or upstream excerpts."""
    capsule={'kind':'extraction_failure_capsule','step':step,'exit_code':exit_code,
             'classification':guard or 'lean_nonzero_exit','stdout_sha256':digest(stdout),
             'stderr_sha256':digest(stderr),'raw_logs_retained':False,'headers':[]}
    if step=='environment' or step.startswith('companion-'):
        allowed={str(tools/'environment_facts.lean'):'companions/environment_facts.lean.txt',
                 str(tools/'source_facts.lean'):'companions/source_facts.lean.txt'}
        allowed.update({str(project/r['path']):'sources/'+r['path'] for r in rows})
        # Lean can render the exact same input path relative to the child cwd.
        # Admit only aliases derived from our allowlist, never arbitrary basenames.
        work=tools.parent/'work'
        for filename,label in list(allowed.items()):
            relative=os.path.relpath(filename,work)
            allowed[relative]=label
            allowed['./'+relative]=label
        seen=set()
        for line in (stderr[:32768]+b'\n'+stdout[:32768]).decode('utf-8',errors='replace').splitlines():
            for filename,label in allowed.items():
                if not line.startswith(filename+':'):continue
                parts=line[len(filename)+1:].split(':',2)
                if len(parts)!=3 or not parts[0].isdigit() or not parts[1].isdigit():continue
                message=parts[2].lstrip()
                if not re.match(r'error(?:\([A-Za-z0-9_.]{1,96}\))?:',message):continue
                message=re.sub(r"(?<![A-Za-z0-9_])/(?:[^\s'\"<>]+)",'<path>',message)[:384]
                key=(label,parts[0],parts[1],message)
                if key in seen:continue
                seen.add(key)
                capsule['headers'].append({'file':label,'line':int(parts[0]),'column':int(parts[1]),'message':message})
                break
            if len(capsule['headers'])==8:break
    encoded=json.dumps(capsule,ensure_ascii=True,separators=(',',':')).encode()
    if len(encoded)>8192:
        capsule['headers']=[]
        encoded=json.dumps(capsule,separators=(',',':')).encode()
    return encoded.decode()


def main(argv=None):
    ap=argparse.ArgumentParser(description=__doc__)
    for flag in ('project','manifest','extractors','toolchain-bin','output'):ap.add_argument('--'+flag,type=Path,required=True)
    for flag in ('wrapper-commit','harness-commit','workflow-run-url'):ap.add_argument('--'+flag,required=True)
    ap.add_argument('--execute',action='store_true');ap.add_argument('--resources-coordinated',action='store_true')
    ap.add_argument('--cpu',type=int);ap.add_argument('--timeout-seconds',type=int,default=1800)
    ap.add_argument('--free-disk-floor-gib',type=float,default=8);ap.add_argument('--memory-floor-gib',type=float,default=1.5)
    args=ap.parse_args(argv)
    if not args.execute or not args.resources_coordinated:ap.error('Both execution/resource flags required; these do not grant permission')
    if args.free_disk_floor_gib<8 or args.memory_floor_gib<1.5 or args.timeout_seconds<1:ap.error('Resource floors cannot be lowered')
    prov=provenance(args.wrapper_commit,args.harness_commit,args.workflow_run_url)
    project,manifest,toolbin,output=(p.resolve() for p in (args.project,args.manifest,args.toolchain_bin,args.output))
    before=snapshot(project);rows=json.loads(manifest.read_text())['modules']
    runtime=preflight_runtime(project,toolbin,rows)
    config=prepare(project,manifest,output,args.extractors);config['provenance']=prov
    work,receipts,tools=output/'work',output/'receipts',output/'tools'
    raw=output/'raw';raw.mkdir()
    records=[]
    env=dict(os.environ,PATH=str(toolbin)+os.pathsep+os.environ.get('PATH',''),LEAN_NUM_THREADS='1',LEAN_IMPORT_WORKERS='1',MATHLIB_NO_CACHE_ON_UPDATE='1')
    env=capture_search_paths(project,toolbin,env)
    affinity={args.cpu} if args.cpu is not None else {max(os.sched_getaffinity(0))}
    if not affinity<=os.sched_getaffinity(0):raise ValueError('CPU affinity unavailable')

    def write(relative,value,jsonl=False):
        data=(('\n'.join(json.dumps(r,ensure_ascii=False,separators=(',',':')) for r in value)) if jsonl else json.dumps(value,indent=2,ensure_ascii=False)).encode()+b'\n'
        destination=receipts/relative
        current=sum(p.stat().st_size for p in receipts.rglob('*') if p.is_file())
        old=destination.stat().st_size if destination.exists() else 0
        if len(data)>PER_FILE_CAP or current-old+len(data)>CAP:raise ValueError('Receipt cap exceeded')
        destination.parent.mkdir(parents=True,exist_ok=True);destination.write_bytes(data)

    def invariant():
        if snapshot(project)!=before or digest(manifest.read_bytes())!=config['source_manifest_sha256']:
            raise ValueError('Candidate file allowlist/content or manifest changed')
        for name,expected in config['tools_sha256'].items():
            if digest((tools/name).read_bytes())!=expected:raise ValueError('Extractor/companion changed')

    def resource_issue():
        if shutil.disk_usage(output).free<args.free_disk_floor_gib*2**30:return 'disk_floor'
        mem=next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
        if mem<args.memory_floor_gib*2**30:return 'memory_floor'
        if sum(p.stat().st_size for p in receipts.rglob('*') if p.is_file())>CAP:return 'receipt_cap'
        return None

    def child_limits():
        os.sched_setaffinity(0,affinity);resource.setrlimit(resource.RLIMIT_FSIZE,(PER_FILE_CAP,PER_FILE_CAP))

    def run(step,arguments):
        invariant()
        if resource_issue():raise ValueError('Resource floor before execution')
        out,err=raw/(step+'.stdout'),raw/(step+'.stderr');began=time.monotonic()
        command=[str(toolbin/'lean'),'--trust=0',*arguments]
        stopped=None
        with out.open('wb') as stdout,err.open('wb') as stderr:
            proc=subprocess.Popen(command,cwd=work,env=env,stdout=stdout,stderr=stderr,start_new_session=True,preexec_fn=child_limits)
            while proc.poll() is None:
                stopped=resource_issue()
                if time.monotonic()-began>args.timeout_seconds:stopped='timeout'
                if stopped:
                    try:os.killpg(proc.pid,signal.SIGTERM)
                    except ProcessLookupError:pass
                    try:proc.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        os.killpg(proc.pid,signal.SIGKILL);proc.wait()
                    break
                time.sleep(0.25)
        replacements={str(project):'<candidate>',str(output):'<output>',str(toolbin):'<toolchain-bin>'}
        symbolic=[]
        for argument in command:
            for path in sorted(replacements,key=len,reverse=True):argument=argument.replace(path,replacements[path])
            symbolic.append(argument)
        records.append({'step':step,'argv_placeholders':symbolic,'cwd_placeholder':'<output>/work','exit_code':proc.returncode,
                        'seconds':round(time.monotonic()-began,3),'stdout_sha256':digest(out.read_bytes()),'stderr_sha256':digest(err.read_bytes())})
        write('commands.json',records)
        if stopped or proc.returncode:
            print(failure_capsule(step,proc.returncode,stopped,out.read_bytes(),err.read_bytes(),project,tools,rows),flush=True)
            err.unlink();out.unlink()
            raise ValueError('Lean process failed; raw diagnostics are excluded from retained artifacts')
        err.unlink()
        invariant();return out

    result={'status':'RUNNING','actual_node_generation':'NOT_RUN','actual_transformed_type_comparison':'NOT_RUN','platform_upload':'NOT_RUN',
            'provenance':prov,'started_utc':datetime.now(timezone.utc).isoformat()}
    write('adapter_receipt.json',config)
    try:
        stdout=run('stage1',[str(tools/'extract_decl_graph.lean')]);stdout.unlink()
        graph=read_jsonl(work/'decl_graph.jsonl');write('decl_graph.jsonl',graph,True)
        stdout=run('environment',[str(tools/'environment_facts.lean')]);metadata=read_jsonl(stdout);stdout.unlink()
        meta={r['name']:r for r in metadata}
        if len(meta)!=len(metadata):raise ValueError('Duplicate environment metadata name')
        names={r['name'] for r in graph}
        if len(names)!=len(graph) or config['target'] not in names:raise ValueError('Graph target/identity failure')
        graph_modules={r['module'] for r in graph}
        if not graph_modules<={r['module'] for r in rows}:raise ValueError('Graph module outside participating closure')
        enriched=[]
        for row in graph:
            peer=meta.get(row['name'])
            if not peer or any(peer[k]!=row[k] for k in ('module','userName','isPrivate')):raise ValueError('Graph/metadata identity mismatch')
            enriched.append({**row,'constructorNames':peer['constructorNames'],'typePretty':peer['typePretty']})
        write('environment_facts.jsonl',[meta[r['name']] for r in graph],True)
        write('planner_graph.jsonl',enriched,True)
        write('original_types.jsonl',[{'name':r['name'],'module':r['module'],'typePretty':r['typePretty']} for r in enriched],True)
        aliases={};private={}
        for row in graph:
            if row['isPrivate']:private.setdefault((row['userName'],row['module']),[]).append(row['name'])
        planner_modules=[]
        for index,row in enumerate(rows):
            slug=f'{index:02d}';source=project/row['path'];data=source.read_bytes()
            stdout=run('oracle-'+slug,['--run',str(tools/'extract_sketch_info.lean'),str(source)])
            ordinary=read_jsonl(stdout);stdout.unlink()
            stdout=run('companion-'+slug,['--run',str(tools/'source_facts.lean'),str(source),row['module']])
            extra=read_jsonl(stdout);stdout.unlink()
            check_positions(ordinary,data);check_positions(extra,data)
            merged=merge_oracles(ordinary,extra,row['module'])
            write(f'sketch/{slug}.jsonl',ordinary,True);write(f'planner_sketch/{slug}.jsonl',merged,True);write(f'companion/{slug}.jsonl',extra,True)
            for ref in (r for r in merged if r['kind']=='ref'):
                key=(ref['userName'],ref['originModule'])
                if key in private and ref['const'] not in names:
                    if len(private[key])!=1:raise ValueError('Private userName/module identity ambiguous')
                    alias={'const':ref['const'],'userName':ref['userName'],'module':ref['originModule']}
                    if ref['const'] in aliases and aliases[ref['const']]!=alias:raise ValueError('Private alias conflict')
                    aliases[ref['const']]=alias
            relative='sources/'+row['path'];dest=receipts/relative;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
            planner_modules.append({'module':row['module'],'source':relative,'source_sha256':row['prove2me_sha256'],
                                    'sketch':f'planner_sketch/{slug}.jsonl','sketch_sha256':digest((receipts/f'planner_sketch/{slug}.jsonl').read_bytes()),
                                    'companion':f'companion/{slug}.jsonl','companion_sha256':digest((receipts/f'companion/{slug}.jsonl').read_bytes()),'reference_filter':None})
        write('private_aliases.json',sorted(aliases.values(),key=lambda r:r['const']))
        write('planner_manifest.json',{'schema_version':1,'provenance_kind':'actual_official_extraction_and_independent_companions',
              'source_repository':config['source_repository'],'source_base_commit':config['source_base_commit'],'source_commit':None,
              'compatibility_snapshot_id':digest(json.dumps(before,sort_keys=True).encode()),'graph_sha256':digest((receipts/'planner_graph.jsonl').read_bytes()),
              'targets':[config['target']],'private_ref_aliases':sorted(aliases.values(),key=lambda r:r['const']),'modules':planner_modules})
        (receipts/'LICENSE').write_bytes((project/'LICENSE').read_bytes())
        invariant()
        if preflight_runtime(project,toolbin,rows)!=runtime:raise ValueError('Runtime/dependencies changed')
        runtime.update(search_path_capture='selected Lean/dynamic-library paths absolutized relative to candidate; values not retained',source_tree_sha256=digest(json.dumps(before,sort_keys=True).encode()))
        write('runtime.json',runtime)
        config['status']='EXECUTED_WITH_SUCCESSFUL_FACT_AGREEMENT'
        config['companions']['Lean_compilation']='PASSED_IN_THIS_RUNTIME'
        config['execution_status']='All 110 Lean commands and official/companion reference comparisons passed'
        write('adapter_receipt.json',config)
        result.update(status='EXTRACTION_PASSED_TRANSFORMS_NOT_RUN',completed_modules=54,source_allowlist_unchanged=True,
                      official_and_companion_reference_agreement=True,finished_utc=datetime.now(timezone.utc).isoformat())
        write('phase_result.json',result)
        info=export(receipts,output/'artifact',config['modules'],config['project_license_sha256'])
        print('EXTRACTION_PASSED_TRANSFORMS_NOT_RUN; validated artifact bytes='+str(info['uncompressed_bytes']))
        return 0
    except Exception:
        # Never retain exception text or failed-run stdout/stderr; they can echo source.
        result.update(status='FAILED_CLOSED',failure_step=records[-1]['step'] if records else 'preflight',finished_utc=datetime.now(timezone.utc).isoformat())
        write('phase_result.json',result)
        print('FAILED_CLOSED; no upload-eligible artifact was produced',file=sys.stderr)
        return 2

if __name__=='__main__':raise SystemExit(main())
