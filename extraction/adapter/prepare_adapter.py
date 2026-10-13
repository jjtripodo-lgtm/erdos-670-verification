#!/usr/bin/env python3
"""Prepare official tools plus independently authored companions. Does not run Lean."""
import argparse
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
PIN='78989800ba0b3149ee34205257025bd0f617e8ef'
DEFAULT_TARGET='Erdos488.Geometry.SeparatedDistances.FixedDimension.fixed_dimension_erdos_670'
EXTRACTOR_HASHES={
 'extract_decl_graph.lean':'e421a1d7bb1847697de699ecc6e9d66a1e47fb17c876e627fd665c4ad68db622',
 'extract_sketch_info.lean':'e0a9164a476c61b6da70592e3c7e8f4267910ac3d433d9fd13e6ccca7b7e801b'}
CONFIG_HASHES={
 'lakefile.toml':'d8914ebe2c7789ee40874913257a3f510fcc3c84449288cf3580975a64614fb3',
 'lake-manifest.json':'c94eed389692ce27a34480450fa1e3c97dbc92fd1b3970603f2ec7cbe31b4b33',
 'lean-toolchain':'3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71',
 'LICENSE':'3587ec3f5eb141a9ec2a9470a10a8cae9bc904db51d2d7d4877bd5ff9751208e'}


def digest(data):return hashlib.sha256(data).hexdigest()


def replace_once(text,old,new):
 if text.count(old)!=1:raise ValueError('Configuration marker is not unique: '+repr(old))
 return text.replace(old,new,1)


def prepare(project,source_manifest,output,extractors):
 project,source_manifest,output,extractors=(p.resolve() for p in (project,source_manifest,output,extractors))
 if output==project or project in output.parents:raise ValueError('Keep prepared tools outside the candidate source root')
 if output.exists():raise ValueError('Use a new output directory')
 manifest=json.loads(source_manifest.read_text()); rows=manifest['modules']
 if len(rows)!=54 or manifest.get('module_count')!=54:raise ValueError('Expected reviewed 54-module closure')
 if {str(p.relative_to(project)) for p in (project/'Erdos488').rglob('*.lean')}!={r['path'] for r in rows}:
  raise ValueError('Manifest/source module sets differ')
 records=[]
 for row in rows:
  path=Path(row['path']); name=row['module']
  if not all(part and not part[0].isdigit() and all(c.isascii() and (c.isalnum() or c=='_') for c in part) for part in name.split('.')):
   raise ValueError('Unsafe module identifier')
  if path.is_absolute() or '..' in path.parts or str(path.with_suffix('')).replace('/','.')!=name:
   raise ValueError('Noncanonical source path')
  full=project/path
  if full.is_symlink() or not full.is_file():raise ValueError('Source must be a regular reviewed file')
  data=full.read_bytes()
  if digest(data)!=row['prove2me_sha256']:raise ValueError('Source differs from reviewed manifest: '+str(path))
  records.append({'module':name,'path':str(path),'sha256':digest(data)})
 if (project/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.33.1':raise ValueError('Expected Lean 4.33.1')
 for name,expected in CONFIG_HASHES.items():
  p=project/name
  if p.is_symlink() or not p.is_file() or digest(p.read_bytes())!=expected:raise ValueError('Frozen reviewed config/license hash mismatch: '+name)
 license_path=project/'LICENSE'
 if not license_path.is_file() or license_path.is_symlink():raise ValueError('Project MIT LICENSE is required')
 license_data=license_path.read_bytes()
 if b'MIT License' not in license_data:raise ValueError('Expected project MIT LICENSE')
 official={}
 for name,wanted in EXTRACTOR_HASHES.items():
  data=(extractors/name).read_bytes()
  if digest(data)!=wanted:raise ValueError('Pinned official reference hash mismatch: '+name)
  official[name]=data
 imports=''.join('import '+r['module']+'\n' for r in records)
 stage1=replace_once(official['extract_decl_graph.lean'].decode(),'import SumSquares\n',imports)
 stage1=replace_once(stage1,'let projPrefix := `SumSquares','let projPrefix := `Erdos488')
 metadata=replace_once((HERE/'companions/environment_facts.lean.txt').read_text(),'-- PROJECT_IMPORTS\n',imports)
 sources={'extract_decl_graph.lean':stage1.encode(),'extract_sketch_info.lean':official['extract_sketch_info.lean'],
          'environment_facts.lean':metadata.encode(),'source_facts.lean':(HERE/'companions/source_facts.lean.txt').read_bytes()}
 (output/'tools').mkdir(parents=True);(output/'receipts').mkdir();(output/'work').mkdir()
 for name,data in sources.items():(output/'tools'/name).write_bytes(data)
 receipt={'schema_version':2,'status':'PREPARED_NOT_EXECUTED','target':DEFAULT_TARGET,
  'source_repository':manifest['source_repository'],'source_base_commit':manifest['source_commit'],
  'source_manifest_sha256':digest(source_manifest.read_bytes()),'modules':records,
  'project_config_sha256':{name:digest((project/name).read_bytes()) for name in ('lean-toolchain','lakefile.toml','lake-manifest.json')},
  'project_license_sha256':digest(license_data),'upstream_commit':PIN,
  'official_tools':[{'file':name,'url':f'https://raw.githubusercontent.com/prove2me/prove2me_workspace/{PIN}/scripts/{name}',
    'original_sha256':EXTRACTOR_HASHES[name],'configured_sha256':digest(sources[name]),
    'changes':['documented root imports: all 54 manifest modules','documented project prefix: Erdos488'] if name=='extract_decl_graph.lean' else []}
    for name in EXTRACTOR_HASHES],
  'tools_sha256':{name:digest(data) for name,data in sources.items()},
  'companions':{'independently_authored':True,'Lean_compilation':'NOT_RUN','source_reelaboration_options':{'autoImplicit':False},
    'purpose':'Exact constructors/types, parser syntax/binding facts and private reference identities; original Stage 2 remains unchanged'},
  'official_stage2_options':'upstream empty options retained; companion independently re-elaborates autoImplicit=false and reference-position agreement is mandatory',
  'execution_status':'No Lean process was launched by preparation','artifact_cap_mib':64}
 (output/'receipts/adapter_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print('Prepared inert extraction bundle; official Stage 2 unchanged; no Lean executed')
 return receipt


def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--project',type=Path,required=True);ap.add_argument('--manifest',type=Path,required=True)
 ap.add_argument('--output',type=Path,required=True);ap.add_argument('--extractors',type=Path,required=True)
 args=ap.parse_args();prepare(args.project,args.manifest,args.output,args.extractors)

if __name__=='__main__':main()
