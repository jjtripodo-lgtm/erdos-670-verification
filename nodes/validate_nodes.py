#!/usr/bin/env python3
"""Exact transformed-text preflight; no platform API, upload, credentials or artifact write."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time

HERE=Path(__file__).resolve().parent
ALLOWED_AXIOMS={'propext','Classical.choice','Quot.sound'}
CAP=4*2**20


def require(test,message):
    if not test:raise ValueError(message)


def digest(data):return hashlib.sha256(data).hexdigest()


def safe_path(name):
    p=PurePosixPath(name)
    require(p.parts and not p.is_absolute() and '..' not in p.parts and str(p)==name and '\\' not in name,'Unsafe path')
    return p


def name_ok(name):
    return bool(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',name))


def inventory(root,allow_build=False):
    out={}
    for directory,dirs,files in os.walk(root,followlinks=False):
        if Path(directory)==root and '.lake' in dirs:
            require(allow_build,'Unexpected build cache directory')
            require(stat.S_ISDIR((root/'.lake').lstat().st_mode),'Build root is a link/special file')
            dirs.remove('.lake')
        for n in dirs:
            require(stat.S_ISDIR((Path(directory)/n).lstat().st_mode),'Directory link/special file')
        for n in files:
            p=Path(directory)/n;s=p.lstat()
            require(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'File link/special file')
            out[str(p.relative_to(root))]={'sha256':digest(p.read_bytes()),'bytes':s.st_size}
    return out


def fixture_map():
    data=json.loads((HERE/'FIXTURE_MAP.json').read_text())
    require(isinstance(data,dict) and len(data)==104,'Expected 104 exact prepared files')
    total=0
    for rel,entry in data.items():
        safe_path(rel);safe_path(entry['fixture'])
        require(set(entry)=={'fixture','sha256','bytes'} and type(entry['bytes']) is int and entry['bytes']>=0,'Invalid fixture entry')
        require(re.fullmatch('[0-9a-f]{64}',entry['sha256']),'Invalid hash')
        total+=entry['bytes']
    require(total<CAP,'Prepared candidate exceeds cap')
    require(len({e['fixture'] for e in data.values()})==len(data),'Duplicate fixture aliases')
    return data


def check(root):
    expected={k:{'sha256':v['sha256'],'bytes':v['bytes']} for k,v in fixture_map().items()}
    require(inventory(root,allow_build=True)==expected,'Prepared candidate changed')
    receipt=json.loads((root/'GENERATION_RECEIPT.json').read_text())
    require(receipt['node_count']==10 and receipt['definition_bundle_count']==28,'Unreviewed decomposition')
    require(receipt['extraction_provenance']['wrapper_commit']=='2b2b59a951c2df97230ab73d7ca50b672941be9e','Wrong extraction provenance')
    require(len(receipt['build_targets'])==48 and all(name_ok(n) for n in receipt['build_targets']),'Invalid build targets')
    for row in receipt['records']:
        require(all(name_ok(n) and n.startswith(('Mathlib.','Definitions.','Theorems.')) for n in row['imports']),'Unexpected import namespace')
        if row['kind']=='definition_bundle':
            require(not any(n.startswith('Theorems.') for n in row['imports']),'Definition imports sorry theorem')
            require(all(name_ok(n) for n in row['axiom_names']),'Invalid definition audit name')
        elif row['kind']=='theorem_node':
            require(name_ok(row['theorem_name']) and row['theorem_module'] not in row['imports'],'Own-target import or invalid name')
            slug=row['theorem_name'].replace('.','_');prefix=root/'Payloads'/slug
            pre=Path(str(prefix)+'.preamble.lean.txt').read_bytes();statement=Path(str(prefix)+'.formal_statement.lean.txt').read_bytes();solution=Path(str(prefix)+'.solution.lean.txt').read_bytes()
            require(digest(pre)==row['preamble_sha256'] and digest(statement)==row['formal_statement_sha256'],'Exact payload part drift')
            require(pre+statement==(root/(row['theorem_module'].replace('.','/')+'.lean')).read_bytes(),'Staged theorem differs from exact upload text')
            require(solution==(root/(row['solution_module'].replace('.','/')+'.lean')).read_bytes(),'Staged solution differs from exact upload text')
        else:raise ValueError('Unknown record kind')
    return receipt


def materialize(output):
    require(not output.exists(),'Fresh candidate directory required')
    source=HERE/'fixtures';mapping=fixture_map()
    require(set(inventory(source))=={v['fixture'] for v in mapping.values()},'Unexpected fixture files')
    output.mkdir(parents=True)
    for rel,entry in mapping.items():
        data=(source/entry['fixture']).read_bytes()
        require(len(data)==entry['bytes'] and digest(data)==entry['sha256'],'Fixture hash mismatch')
        p=output/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    check(output)
    print('PASS: exact 104-file candidate materialized; Lean checks not run')


def guard(root):
    require(shutil.disk_usage(root).free>=8*2**30,'Need at least 8 GiB free; no automatic cleanup')
    avail=next(int(s.split()[1])*1024 for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:'))
    require(avail>=1.5*2**30,'Need at least 1.5 GiB available memory')


def execute(argv,cwd,timeout=1200):
    guard(cwd);print('+ '+' '.join(map(str,argv)),flush=True)
    with tempfile.TemporaryFile() as log:
        proc=subprocess.Popen(argv,cwd=cwd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        start=time.monotonic()
        try:
            while proc.poll() is None:
                guard(cwd);require(time.monotonic()-start<timeout,'Command timeout')
                require(os.fstat(log.fileno()).st_size<=16*2**20,'Compiler output cap exceeded')
                time.sleep(1)
        except BaseException:
            os.killpg(proc.pid,signal.SIGTERM)
            try:proc.wait(timeout=10)
            except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
            raise
        log.seek(0);data=log.read();text=data.decode('utf-8',errors='replace')
        if proc.returncode:
            print(text[-16384:],flush=True)
            raise RuntimeError('Command exit '+str(proc.returncode))
        return text


def axioms(output,name):
    found=re.findall(re.escape(name)+r"['’]?\s+depends on axioms:\s*\[([^\]]*)\]",output)
    if len(found)==1:return {x.strip() for x in found[0].split(',') if x.strip()}
    if not found and re.search(re.escape(name)+r"['’]?\s+does not depend on any axioms",output):return set()
    raise ValueError('Missing/ambiguous axiom report for '+name)


def validate_runtime(root,verifier):
    receipt=check(root)
    version=execute(['lean','--version'],root).strip()
    require(re.search(r'\bversion 4\.33\.1(?:,|\s)',version),'Wrong Lean version')
    sys.path.insert(0,str(verifier/'scripts'))
    from run_checks import dependencies
    dependencies(root,fetch=False)
    return receipt,version


def main(argv=None):
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('phase',choices=['materialize','dependencies','cache','validate'])
    ap.add_argument('--candidate',type=Path,required=True)
    ap.add_argument('--verifier',type=Path)
    ap.add_argument('--execute',action='store_true',help='Required for network/build phases; does not grant authorization')
    args=ap.parse_args(argv);root=args.candidate.resolve()
    if args.phase=='materialize':materialize(root);return 0
    require(args.execute and args.verifier is not None,'Execution and exact public verifier required')
    verifier=args.verifier.resolve()
    require(subprocess.check_output(['git','-C',str(verifier),'rev-parse','HEAD'],text=True).strip()=='5510ffd94156d48dbe393ac619586b935212da79','Wrong frozen helper commit')
    receipt=check(root);guard(root)
    sys.path.insert(0,str(verifier/'scripts'))
    from run_checks import dependencies
    if args.phase=='dependencies':
        dependencies(root,fetch=True);check(root);guard(root);return 0
    receipt,version=validate_runtime(root,verifier)
    if args.phase=='cache':
        output=execute(['lake','exe','cache','--repo=leanprover-community/mathlib4','--cache-from=master,legacy','get',*receipt['external_imports']],root)
        print(output[-4096:]);check(root);guard(root);return 0
    report={'kind':'node_validation','source_commit':os.environ.get('GITHUB_SHA'),'lean_version':version,
            'status':'RUNNING','definition_count':28,'node_count':10,'platform_upload':'NOT_RUN','types':[],'definition_axioms':{}}
    try:
        for module in receipt['build_targets']:
            execute(['lake','--no-cache','build',module],root)
            print('COMPILED '+module,flush=True);check(root)
        original={r['name']:r['typePretty'] for r in json.loads((root/'original_node_types.json').read_text())}
        with tempfile.TemporaryDirectory(prefix='fixed670-node-probes-') as temporary:
            tmp=Path(temporary)
            defs=[r for r in receipt['records'] if r['kind']=='definition_bundle']
            names=[n for r in defs for n in r['axiom_names']]
            audit=''.join('import '+r['module']+'\n' for r in defs)+'\n'+''.join('#print axioms '+n+'\n' for n in names)
            path=tmp/'DefinitionsAxioms.lean';path.write_text(audit)
            output=execute(['lake','--no-cache','env','lean','--trust=0',str(path)],root)
            for n in names:
                ax=axioms(output,n);require(ax<=ALLOWED_AXIOMS,'Definition proof has unpermitted axiom')
                report['definition_axioms'][n]=sorted(ax)
            for row in receipt['records']:
                if row['kind']!='theorem_node':continue
                name=row['theorem_name'];slug=name.replace('.','_')
                for kind,decl in [('statement',name),('solution','solution')]:
                    source=(root/'Probes'/(slug+'_'+kind+'.lean.txt')).read_text()+'\n#print axioms '+decl+'\n'
                    path=tmp/(slug+'_'+kind+'.lean');path.write_text(source)
                    output=execute(['lake','--no-cache','env','lean','--trust=0',str(path)],root)
                    facts=[]
                    for line in output.splitlines():
                        try:value=json.loads(line)
                        except json.JSONDecodeError:continue
                        if isinstance(value,dict) and set(value)=={'name','key','typePretty'}:facts.append(value)
                    require(len(facts)==1 and facts[0]['name']==decl and facts[0]['key']==name+'::'+kind,'Missing/ambiguous exact type record')
                    same=facts[0]['typePretty']==original[name]
                    if not same:
                        import difflib
                        print('\n'.join(difflib.unified_diff(original[name].splitlines(),facts[0]['typePretty'].splitlines(),fromfile='original type',tofile='staged type'))[:16384])
                    require(same,'Exact original/staged type differs; even universe display changes require review')
                    ax=axioms(output,decl)
                    permitted=ALLOWED_AXIOMS|({'sorryAx'} if kind=='statement' or row['reductions'] else set())
                    require(ax<=permitted,'Unpermitted staged axiom')
                    report['types'].append({'node':name,'kind':kind,'exact_type_sha256':digest(facts[0]['typePretty'].encode()),'axioms':sorted(ax),'reductions':row['reductions'] if kind=='solution' else []})
                    print('TYPE_MATCH '+name+' '+kind,flush=True)
        check(root);dependencies(root,fetch=False)
        require(len(report['types'])==20 and len(report['definition_axioms'])==92,'Incomplete exact-text checks')
        report['status']='EXACT_TRANSFORMED_BUILD_TYPES_AND_AXIOMS_PASS'
        report['note']='Theorem stubs intentionally contain sorry. Solution dependency stubs are intended platform reductions; this is preflight, not platform acceptance.'
        return 0
    except Exception:
        report['status']='FAILED_CLOSED'
        raise
    finally:
        print('NODE_VALIDATION_REPORT '+json.dumps(report,sort_keys=True,separators=(',',':')),flush=True)


if __name__=='__main__':raise SystemExit(main())
