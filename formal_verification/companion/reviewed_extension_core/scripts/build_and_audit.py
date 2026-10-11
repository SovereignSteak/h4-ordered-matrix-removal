#!/usr/bin/env python3
"""Fresh sequential build of the isolated extension core; dependency oleans only may be shared."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,sys,datetime,time
ROOT=Path(__file__).resolve().parent.parent
OUT=ROOT/'evidence'
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def files():return sorted((ROOT/'H4Formal').rglob('*.lean'))+[ROOT/'H4Formal.lean',ROOT/'ExtensionAudit.lean',ROOT/'lean-toolchain',ROOT/'lakefile.toml',ROOT/'lake-manifest.json',Path(__file__).resolve()]
def source_hashes():return {str(p.relative_to(ROOT)):sha(p) for p in files()}
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--dependency-root',type=Path,required=True,help='Pinned .lake/packages directory only; never another project build directory.');ap.add_argument('--lean',type=Path,default=Path(shutil.which('lean') or 'lean'));ap.add_argument('--clean',action='store_true',required=True);args=ap.parse_args()
 OUT.mkdir(exist_ok=True);report={'status':'RUNNING','started_at_utc':now(),'scope':'34 certificate-free derived extension modules and top-level declaration audit','original_companion_modified':False,'independence':'Fresh same-host sequential compile of derived core, not full companion or independently administered review.','source_sha256':source_hashes(),'commands':[]};rp=OUT/'extension_build_run.json'
 def save():rp.write_text(json.dumps(report,indent=2)+'\n')
 def run(argv,log,env=None):
  rec={'argv':[str(x) for x in argv],'started_at_utc':now(),'log':log};report['commands'].append(rec);save();print('RUN',' '.join(rec['argv']),flush=True)
  with (OUT/log).open('w') as f:ret=subprocess.run(rec['argv'],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,env=env)
  rec.update(finished_at_utc=now(),exit_code=ret.returncode);save()
  if ret.returncode:raise RuntimeError('Failed: '+log+'\n'+(OUT/log).read_text()[-6000:])
 save()
 try:
  run([args.lean,'--version'],'lean_version.log')
  if not (OUT/'lean_version.log').read_text().startswith('Lean (version 4.24.0,'):raise RuntimeError('Wrong Lean version')
  report['lean']={'path':str(args.lean.resolve()),'sha256':sha(args.lean.resolve())}
  # Verify recorded external source revisions; only official external build paths enter LEAN_PATH.
  manifest=json.loads((ROOT/'lake-manifest.json').read_text());deps=[];paths=[]
  for dep in manifest['packages']:
   p=(args.dependency_root/dep['name']).resolve();head=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
   if head!=dep['rev']:raise RuntimeError('Dependency revision mismatch: '+dep['name'])
   subprocess.run(['git','-C',str(p),'diff','--quiet','HEAD','--'],check=True)
   d=p/'.lake/build/lib/lean'
   if d.exists():
    if (d/'H4Formal').exists() or (d/'H4Formal.olean').exists():raise RuntimeError('Namespace contamination in '+str(d))
    paths.append(str(d))
   deps.append({'name':dep['name'],'revision':head,'source':str(p),'library':str(d)})
  report['dependencies']=deps
  build=ROOT/'.lake/build';report['preclean_oleans']=len(list(build.rglob('*.olean'))) if build.exists() else 0
  if build.exists():shutil.rmtree(build)
  lib=build/'lib/lean';lib.mkdir(parents=True)
  report['after_clean_oleans']=0;report['clean_finished_at_utc']=now()
  env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(lib)]+paths);env.pop('LEAN_SRC_PATH',None);report['LEAN_PATH']=env['LEAN_PATH']
  # Record exact external .olean/.olean.private/.olean.server artifacts reachable from project imports.
  project={'.'.join(p.relative_to(ROOT).with_suffix('').parts):p for p in sorted((ROOT/'H4Formal').rglob('*.lean'))};project['H4Formal']=ROOT/'H4Formal.lean'
  graph={m:re.findall(r'^import\s+(\S+)',p.read_text(),re.M) for m,p in project.items()}
  order=[];seen=set()
  def visit(m):
   if m in seen:return
   seen.add(m)
   for d in graph[m]:
    if d in project:visit(d)
   order.append(m)
  visit('H4Formal')
  if set(order)!=set(project):raise RuntimeError('Orphan source or incomplete dependency order')
  report['build_order']=order;report['project_modules']=len(order);save()
  for i,m in enumerate(order,1):
   src=project[m];target=lib/Path(*m.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
   run([args.lean,'-j1','-s65536','-o',target,str(src.relative_to(ROOT))],f'{i:02d}_{m}.log',env)
  run([args.lean,'-j1','-s65536','-o',lib/'ExtensionAudit.olean','ExtensionAudit.lean'],'extension_audit.log',env)
  if source_hashes()!=report['source_sha256']:raise RuntimeError('Derived source changed during build')
  prov=json.loads((OUT/'source_provenance.json').read_text())
  for rec in prov['files']:
   if sha(ROOT.parent/'formalized_extensions'/rec['original'])!=rec['original_sha256']:raise RuntimeError('Original companion changed: '+rec['original'])
  audit=json.loads((OUT/'extension_axiom_audit.json').read_text())
  if audit['status']!='DERIVED_EXTENSION_ALL_DECLARATIONS_STANDARD_AXIOM_PASS':raise RuntimeError('Axiom audit did not pass')
  report.update(status='FRESH_DERIVED_EXTENSION_CORE_VERIFIED',finished_at_utc=now(),project_modules_freshly_compiled=len(order),audit_module_compiled=True,compiled_artifacts_sha256={str(p.relative_to(ROOT)):sha(p) for p in sorted(lib.rglob('*.olean*'))},audit_sha256=sha(OUT/'extension_axiom_audit.json'),declarations_audited=audit['project_declarations_audited'],theorems_audited=audit['project_theorems_audited']);save();print(report['status'],flush=True)
 except BaseException as e:
  report.update(status='FAILED',finished_at_utc=now(),error=str(e));save();raise
if __name__=='__main__':main()
