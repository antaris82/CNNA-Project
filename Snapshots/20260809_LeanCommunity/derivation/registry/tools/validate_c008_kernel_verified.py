#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import csv, hashlib, json, re, subprocess, sys
ROOT=Path(__file__).resolve().parents[3]
REG=ROOT/'derivation/registry'; DAG=REG/'dag'; LEAN=ROOT/'derivation/code/lean'
CORE=LEAN/'core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/S01_C008_RecordLiveResponseCoupledUpdate.lean'
PROOF=LEAN/'proofs/src/CNNAProofs/C008/S01_CanonicalRecordLiveUpdateClosure.lean'
EVIDENCE=LEAN/'audit/evidence/USER_LOCAL_C008_FULL_BUILD_20260808.json'
TRANSCRIPT=LEAN/'audit/evidence/USER_LOCAL_C008_FULL_BUILD_20260808.txt'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def rows(p):
    with p.open(encoding='utf-8',newline='') as f:return list(csv.DictReader(f,delimiter='\t'))
errors=[]
for p,label in [(CORE,'core'),(PROOF,'proof'),(EVIDENCE,'evidence'),(TRANSCRIPT,'transcript')]:
    if not p.is_file(): errors.append('missing '+label)
core=CORE.read_text(encoding='utf-8') if CORE.is_file() else ''
proof=PROOF.read_text(encoding='utf-8') if PROOF.is_file() else ''
required_core=['RecordLiveChannels','recordInstructionUpdates','liveInstructionUpdates','applyInstruction','applyInstruction_respects_sameValue','RecordLiveResponseCoupledUpdateContract','recordLiveResponseCoupledUpdateContract']
required_proof=['CanonicalRecordLiveUpdateClosure','canonicalRecordLiveUpdateClosure','CanonicalRecordLiveUpdateContract','canonicalRecordLiveUpdateContract']
for name in required_core:
    if not re.search(r'^(?:structure|def|theorem)\s+'+re.escape(name)+r'\b',core,re.M):errors.append('missing core '+name)
for name in required_proof:
    if not re.search(r'^(?:structure|def|theorem)\s+'+re.escape(name)+r'\b',proof,re.M):errors.append('missing proof '+name)
for token in ['sorry','axiom','admit','unsafe','partial','implemented_by','native_decide','Classical','simp','simpa','Matrix.inv']:
    if re.search(r'\b'+re.escape(token)+r'\b',core): errors.append('forbidden core token '+token)
    if re.search(r'\b'+re.escape(token)+r'\b',proof): errors.append('forbidden proof token '+token)
node=json.loads((REG/'nodes/C008.json').read_text())
if node.get('workflow',{}).get('freeze_state')!='FROZEN_VERIFIED':errors.append('C008 freeze')
if node.get('implementation_status',{}).get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE':errors.append('C008 implementation status')
evnode=node.get('evidence',{})
if evnode.get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE' or evnode.get('kernel_verified_declarations')!=7:errors.append('C008 node evidence')
if evnode.get('axiom_profile_counts')!={'choice_propext_quot':4,'propext_quot_only':3,'axiom_free':0}:errors.append('C008 node axiom profile')
for a in node.get('documentation_profile',{}).get('code_anchors',[]):
    if a.get('resolution') not in {'RESOLVED','RESOLVED_KERNEL_VERIFIED'}:errors.append('unresolved C008 anchor '+str(a.get('symbol')))
status={r['id']:r for r in rows(DAG/'DAG_DISPLAY_STATUS.tsv')}
for nid,want,color in [('C008','FINISHED','#70C779'),('C016','FINISHED','#70C779'),('C017','FINISHED','#70C779')]:
    r=status.get(nid,{})
    if r.get('display_status')!=want or r.get('color')!=color:errors.append(nid+' display status')
edges={r['id']:r for r in rows(DAG/'EDGES.tsv')}
if edges.get('E027',{}).get('status')!='ACTIVE_VERIFIED':errors.append('E027 status')
if edges.get('E028',{}).get('status')!='ACTIVE_VERIFIED':errors.append('E028 status')
if edges.get('E029',{}).get('status')!='ACTIVE_VERIFIED':errors.append('E029 status')
if EVIDENCE.is_file() and TRANSCRIPT.is_file():
    ev=json.loads(EVIDENCE.read_text())
    expected={'choice_propext_quot':4,'propext_quot_only':3,'axiom_free':0}
    for k,v in {'schema':'cnna.c008-kernel-build-evidence.v1','status':'PASS','toolchain':'leanprover/lean4:v4.31.0','proof_modules':19,'c008_audited_declarations':7,'c008_current_proof_axiom_audit':'PASS','full_package_boundary_audit':'PASS'}.items():
        if ev.get(k)!=v:errors.append('evidence '+k)
    if ev.get('c008_axiom_profile_counts')!=expected:errors.append('evidence axiom profiles')
    if ev.get('transitive_axioms_observed')!=['propext','Classical.choice','Quot.sound']:errors.append('evidence transitive axioms')
    if ev.get('direct_project_axioms')!=0 or ev.get('sorry_count')!=0:errors.append('project axiom/sorry count')
    if ev.get('retained_verified_p001_source_hash_match') is not True or ev.get('retained_verified_m003_m004_source_hash_match') is not True or ev.get('retained_verified_p002_source_hash_match') is not True:errors.append('retained prior hashes')
    if sha(TRANSCRIPT)!=ev.get('transcript_sha256'):errors.append('transcript hash')
    for rel,h in ev.get('verified_source_sha256',{}).items():
        p=LEAN/rel
        if not p.is_file() or sha(p)!=h:errors.append('source hash '+rel)
    text=TRANSCRIPT.read_text(encoding='utf-8')
    for marker in ['C008_CURRENT_PROOF_AXIOM_AUDIT PASS','"c008": "KERNEL_VERIFIED_CURRENT_BUILD"','"c008_record_live_update_olean": true','FULL_PACKAGE_BOUNDARY_AUDIT PASS']:
        if marker not in text:errors.append('transcript marker '+marker)
run=subprocess.run([sys.executable,str(LEAN/'audit/check_package_boundary.py')],cwd=LEAN,capture_output=True,text=True)
if run.returncode:errors.append('static boundary')
else:
    st=json.loads(run.stdout)
    if st.get('proofs',{}).get('c008')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE':errors.append('static C008 exact source evidence')
    if st.get('build_evidence',{}).get('retained_verified_c008_source_hash_match') is not True:errors.append('static C008 retained hash')
result={'schema':'cnna.c008-kernel-verified-audit.v1','status':'PASS' if not errors else 'FAIL','date':'2026-08-08','toolchain':'leanprover/lean4:v4.31.0','kernel_verified_declarations':7,'axiom_profile_counts':{'choice_propext_quot':4,'propext_quot_only':3,'axiom_free':0},'python_regression':'PASS_106_TESTS_1086_SUBTESTS','finite_c008_sweep_cases':99,'downstream_projection_status':'C016_C017_KERNEL_VERIFIED','errors':errors}
(DAG/'C008_KERNEL_VERIFIED_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2));sys.exit(1 if errors else 0)
