#!/usr/bin/env python3
"""Compile the isolated exact-transversal supplement against fresh primary imports.
Default requires completed primary build and closes exhaustion unconditionally.
--conditional-only is an explicit intermediate status, never unconditional proof.
"""
import argparse
from datetime import datetime,timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT=Path(__file__).resolve().parent.parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.now(timezone.utc).isoformat()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--primary-root',type=Path,required=True)
    ap.add_argument('--lean',type=Path,required=True);ap.add_argument('--conditional-only',action='store_true');args=ap.parse_args()
    primary=args.primary_root.resolve();lean=args.lean.resolve();out=ROOT/'evidence';out.mkdir(exist_ok=True)
    mode='conditional' if args.conditional_only else 'unconditional';path=out/(mode+'_build_run.json')
    source_names=['ExactTransversal.lean','AuditConditional.lean','scripts/build_and_audit.py']
    if not args.conditional_only:source_names+=['ExactTransversalMain.lean','AuditUnconditional.lean']
    sources={n:sha(ROOT/n) for n in source_names}
    report={'status':'RUNNING','mode':mode,'started_at_utc':now(),'source_sha256':sources,
       'primary_root':str(primary),'lean_sha256':sha(lean),'commands':[],'scope':'Separate supplement; incoming 550 primary files unchanged'}
    def save():path.write_text(json.dumps(report,indent=2)+'\n')
    def run(argv,log,env):
        row={'argv':list(map(str,argv)),'started_at_utc':now(),'log':log};report['commands'].append(row);save()
        with (out/log).open('w') as f:result=subprocess.run(argv,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
        row.update(exit_code=result.returncode,finished_at_utc=now());save()
        if result.returncode:raise RuntimeError('Compile failed: '+log)
    save()
    try:
        pr=json.loads((primary/'evidence/strict_build/strict_build_run.json').read_text())
        allowed=('RUNNING','FRESH_ALL_PROJECT_MODULES_VERIFIED') if args.conditional_only else ('FRESH_ALL_PROJECT_MODULES_VERIFIED',)
        if pr['status'] not in allowed:raise RuntimeError('Required primary build state unavailable')
        if not pr.get('clean_finished_at_utc'):raise RuntimeError('No primary clean-build marker')
        clean=datetime.fromisoformat(pr['clean_finished_at_utc']).timestamp()
        manifest=json.loads((primary/'lake-manifest.json').read_text())
        deps=[primary/'.lake/packages'/d['name']/'.lake/build/lib/lean' for d in manifest['packages']]
        build=ROOT/'.lake/build/lib/lean'
        if (ROOT/'.lake/build').exists():shutil.rmtree(ROOT/'.lake/build')
        build.mkdir(parents=True)
        env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[build,primary/'.lake/build/lib/lean']+deps));report['LEAN_PATH']=env['LEAN_PATH']
        version=subprocess.check_output([lean,'--version'],text=True)
        if not version.startswith('Lean (version 4.24.0,'):raise RuntimeError('Unexpected Lean version')
        report['lean_version']=version.strip();save()
        run([lean,'-j1','-s65536','-o',build/'ExactTransversal.olean','ExactTransversal.lean'],mode+'_core.log',env)
        if args.conditional_only:
            audit_name='AuditConditional';audit_json='conditional_axiom_audit.json';expected='CONDITIONAL_TRANSVERSAL_ALL_DECLARATIONS_STANDARD_AXIOM_PASS'
        else:
            run([lean,'-j1','-s65536','-o',build/'ExactTransversalMain.olean','ExactTransversalMain.lean'],mode+'_main.log',env)
            audit_name='AuditUnconditional';audit_json='unconditional_axiom_audit.json';expected='EXACT_TRANSVERSAL_ALL_DECLARATIONS_STANDARD_AXIOM_PASS'
        run([lean,'-j1','-s65536','-o',build/(audit_name+'.olean'),audit_name+'.lean'],mode+'_audit.log',env)
        audit=json.loads((out/audit_json).read_text())
        if audit['status']!=expected or set(audit['axioms_in_dependency_closure'])-{'propext','Classical.choice','Quot.sound'}:raise RuntimeError('Axiom audit did not pass')
        imports={}
        for m in audit['imported_modules']:
            if m=='H4Formal' or m.startswith('H4Formal.'):
                n=m.replace('.','/')+'.lean';src=primary/n;obj=primary/'.lake/build/lib/lean'/Path(n).with_suffix('.olean')
                source_hash=sha(src)
                if pr['source_sha256'].get(n)!=source_hash:raise RuntimeError('Primary source differs: '+n)
                if obj.stat().st_mtime<clean:raise RuntimeError('Primary artifact predates clean rebuild: '+n)
                imports[n]={'source_sha256':source_hash,'olean_sha256':sha(obj)}
        if {n:sha(ROOT/n) for n in source_names}!=sources:raise RuntimeError('Supplement changed during build')
        report.update(status='CONDITIONAL_TRANSVERSAL_VERIFIED' if args.conditional_only else 'FRESH_EXACT_TRANSVERSAL_SUPPLEMENT_VERIFIED',
            finished_at_utc=now(),axiom_audit_sha256=sha(out/audit_json),primary_imports=imports,
            compiled_artifacts_sha256={str(p.relative_to(ROOT)):sha(p) for p in build.rglob('*.olean')},
            declarations_audited=audit['declarations_audited'],theorems_audited=audit['theorems_audited'],
            exhaustion_discharged=not args.conditional_only,primary_build_report_sha256=sha(primary/'evidence/strict_build/strict_build_run.json'))
        save();print(report['status'])
    except BaseException as e:report.update(status='FAILED',finished_at_utc=now(),error=str(e));save();raise
if __name__=='__main__':main()
