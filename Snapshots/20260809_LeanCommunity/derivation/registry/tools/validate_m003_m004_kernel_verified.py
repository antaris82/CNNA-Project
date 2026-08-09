#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import csv, hashlib, json, subprocess, sys
ROOT=Path(__file__).resolve().parents[3]; LEAN=ROOT/'derivation/code/lean'; REG=ROOT/'derivation/registry'; DOC=REG/'documentation'
E=LEAN/'audit/evidence/USER_LOCAL_M003_M004_FULL_BUILD_20260806.json'; T=LEAN/'audit/evidence/USER_LOCAL_M003_M004_FULL_BUILD_20260806.txt'; OUT=DOC/'M003_M004_CURRENT_AUDIT.json'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def rows(p):
    with p.open(encoding='utf-8',newline='') as f:return list(csv.DictReader(f,delimiter='\t'))
errors=[]
if not E.is_file() or not T.is_file(): errors.append('authoritative M003/M004 evidence missing'); ev={}
else: ev=json.loads(E.read_text(encoding='utf-8'))
expected={'choice_propext_quot':6,'propext_quot_only':5,'axiom_free':0}
for k,v in {'schema':'cnna.m003-m004-kernel-build-evidence.v1','status':'PASS','toolchain':'leanprover/lean4:v4.31.0','proof_modules':15,'m003_m004_proof_declarations':11,'m003_m004_current_proof_axiom_audit':'PASS','full_package_boundary_audit':'PASS'}.items():
    if ev.get(k)!=v: errors.append('evidence '+k)
if ev.get('m003_m004_axiom_profile_counts')!=expected: errors.append('axiom profiles')
if E.is_file() and T.is_file() and ev.get('transcript_sha256')!=sha(T): errors.append('transcript hash')
for rel,h in ev.get('verified_source_sha256',{}).items():
    p=LEAN/rel
    if not p.is_file() or sha(p)!=h: errors.append('source '+rel)
text=T.read_text(encoding='utf-8') if T.is_file() else ''
for marker in ['Build completed successfully (8596 jobs).','M003_M004_CURRENT_PROOF_AXIOM_AUDIT PASS','"m003": "KERNEL_VERIFIED_CURRENT_BUILD"','"m004": "KERNEL_VERIFIED_CURRENT_BUILD"','"m003_canonical_closure_olean": true','"m004_canonical_closure_handoff_olean": true','FULL_PACKAGE_BOUNDARY_AUDIT PASS']:
    if marker not in text: errors.append('marker '+marker)
run=subprocess.run([sys.executable,str(LEAN/'audit/check_package_boundary.py')],cwd=LEAN,capture_output=True,text=True)
if run.returncode: errors.append('static boundary')
else:
    static=json.loads(run.stdout)
    if static.get('proofs',{}).get('m003')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE': errors.append('static M003')
    if static.get('proofs',{}).get('m004')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE': errors.append('static M004')
    if static.get('build_evidence',{}).get('retained_verified_m003_m004_source_hash_match') is not True: errors.append('exact source binding')
for n,count in [('M003',4),('M004',7)]:
    node=json.loads((REG/'nodes'/f'{n}.json').read_text(encoding='utf-8'))
    lean=node.get('evidence',{}).get('lean',{})
    if lean.get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE' or lean.get('proof_declarations')!=count: errors.append(n+' node evidence')
    if node.get('workflow',{}).get('freeze_state')!='FROZEN_VERIFIED': errors.append(n+' freeze')
    if node.get('implementation_status',{}).get('status')!='KERNEL_VERIFIED': errors.append(n+' implementation')
result={'schema':'cnna.m003-m004-current-audit.v1','status':'PASS' if not errors else 'FAIL','date':'2026-08-06','toolchain':'leanprover/lean4:v4.31.0','proof_modules':2,'kernel_verified_declarations':11,'axiom_profile_counts':expected,'exact_source_evidence':'MATCH','errors':errors}
OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(json.dumps(result,indent=2));sys.exit(1 if errors else 0)
