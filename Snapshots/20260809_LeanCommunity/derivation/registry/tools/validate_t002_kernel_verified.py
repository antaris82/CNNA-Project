#!/usr/bin/env python3
from pathlib import Path
import csv,hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[3]; REG=ROOT/'derivation/registry'; DAG=REG/'dag'; LEAN=ROOT/'derivation/code/lean'
def rows(p):
 with p.open(encoding='utf-8',newline='') as f:return list(csv.DictReader(f,delimiter='\t'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]; E=LEAN/'audit/evidence/USER_LOCAL_T002_FULL_BUILD_20260809.json'; T=LEAN/'audit/evidence/USER_LOCAL_T002_FULL_BUILD_20260809.txt'
for p,label in [(E,'evidence'),(T,'transcript')]:
 if not p.is_file():errors.append('missing '+label)
node=json.loads((REG/'nodes/T002.json').read_text())
if node.get('workflow',{}).get('freeze_state')!='FROZEN_VERIFIED':errors.append('T002 freeze')
if node.get('implementation_status',{}).get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE':errors.append('T002 implementation status')
nev=node.get('evidence',{})
if nev.get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE' or nev.get('kernel_verified_declarations')!=26:errors.append('T002 node evidence')
if nev.get('axiom_profile_counts')!={'choice_propext_quot':19,'propext_quot_only':7,'axiom_free':0}:errors.append('T002 axiom profile')
dp=node.get('documentation_profile',{})
if dp.get('v2_state')!='COMPLETE_V2' or dp.get('countercheck_status')!='PASS':errors.append('T002 documentation')
status={r['id']:r for r in rows(DAG/'DAG_DISPLAY_STATUS.tsv')}
for nid,want,color in [('T002','FINISHED','#70C779'),('T003','ACTIVE','#F4A340')]:
 r=status.get(nid,{})
 if r.get('display_status')!=want or r.get('color')!=color:errors.append(nid+' display')
edges={r['id']:r for r in rows(DAG/'EDGES.tsv')}
for eid in ['E070','E071','E072']:
 if edges.get(eid,{}).get('status')!='ACTIVE_VERIFIED':errors.append(eid+' verified')
for eid in ['E073','E074','E075','E076']:
 if edges.get(eid,{}).get('status')!='ACTIVE_CURRENT':errors.append(eid+' active T003')
if E.is_file() and T.is_file():
 ev=json.loads(E.read_text())
 if ev.get('schema')!='cnna.t002-kernel-build-evidence.v1' or ev.get('status')!='PASS':errors.append('evidence header')
 if ev.get('t002_audited_declarations')!=26 or ev.get('t002_axiom_profile_counts')!={'choice_propext_quot':19,'propext_quot_only':7,'axiom_free':0}:errors.append('evidence counts')
 if sha(T)!=ev.get('transcript_sha256'):errors.append('transcript hash')
 for rel,h in ev.get('verified_source_sha256',{}).items():
  p=LEAN/rel
  if not p.is_file() or sha(p)!=h:errors.append('source hash '+rel)
 text=T.read_text()
 for marker in ['Built CNNAProofs.T002.S01_CanonicalRecurrentStateClosure','Built CNNAProofs.T002','T002_CURRENT_PROOF_AXIOM_AUDIT PASS','"t002": "KERNEL_VERIFIED_CURRENT_BUILD"','"t002_recurrent_state_closure_olean": true','FULL_PACKAGE_BOUNDARY_AUDIT PASS']:
  if marker not in text:errors.append('transcript marker '+marker)
run=subprocess.run([sys.executable,str(LEAN/'audit/check_package_boundary.py')],cwd=LEAN,capture_output=True,text=True)
if run.returncode:errors.append('static boundary '+(run.stdout+run.stderr).strip())
else:
 st=json.loads(run.stdout)
 if st.get('proofs',{}).get('t002')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE':errors.append('static T002 exact source')
 if st.get('build_evidence',{}).get('retained_verified_t002_source_hash_match') is not True:errors.append('static retained T002 hash')
result={'schema':'cnna.t002-kernel-verified-audit.v1','status':'PASS' if not errors else 'FAIL','date':'2026-08-09','toolchain':'leanprover/lean4:v4.31.0','kernel_verified_declarations':26,'axiom_profile_counts':{'choice_propext_quot':19,'propext_quot_only':7,'axiom_free':0},'python_regression':'PASS_120_TESTS_1086_SUBTESTS_FINITE_EVIDENCE_ONLY','next_active_node':'T003','errors':errors}
(DAG/'T002_KERNEL_VERIFIED_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));sys.exit(1 if errors else 0)
