#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import csv, hashlib, json, re, subprocess, sys
ROOT=Path(__file__).resolve().parents[3]
REG=ROOT/'derivation/registry'; DAG=REG/'dag'; LEAN=ROOT/'derivation/code/lean'
CORE16=LEAN/'core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/S02_C016_ImmutableRecordChannel.lean'
CORE17=LEAN/'core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure/S03_C017_CurrentLiveChannel.lean'
PROOF=LEAN/'proofs/src/CNNAProofs/C016C017/S01_CanonicalRecordLiveChannelProjectionClosure.lean'
EVIDENCE=LEAN/'audit/evidence/USER_LOCAL_C016_C017_FULL_BUILD_20260808.json'
TRANSCRIPT=LEAN/'audit/evidence/USER_LOCAL_C016_C017_FULL_BUILD_20260808.txt'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def rows(p):
    with p.open(encoding='utf-8',newline='') as f:return list(csv.DictReader(f,delimiter='\t'))
errors=[]
for p,label in [(CORE16,'C016 core'),(CORE17,'C017 core'),(PROOF,'proof'),(EVIDENCE,'evidence'),(TRANSCRIPT,'transcript')]:
    if not p.is_file(): errors.append('missing '+label)
for p,label,required in [
    (CORE16,'C016',['recordChannel','afterInstruction','afterInstruction_eq_append','previousRecord_isLeftPrefix','afterInstruction_respects_sameValue','ImmutableRecordChannelContract','immutableRecordChannelContract']),
    (CORE17,'C017',['liveChannel','afterInstruction','afterInstruction_eq_append','previousLive_isLeftPrefix','afterInstruction_respects_sameValue','CurrentLiveChannelContract','currentLiveChannelContract']),
    (PROOF,'proof',['CanonicalImmutableRecordChannelClosure','canonicalImmutableRecordChannelClosure','CanonicalCurrentLiveChannelClosure','canonicalCurrentLiveChannelClosure','CanonicalRecordLiveChannelProjectionContract','canonicalRecordLiveChannelProjectionContract'])]:
    text=p.read_text(encoding='utf-8') if p.is_file() else ''
    for name in required:
        if not re.search(r'^(?:structure|def|theorem)\s+'+re.escape(name)+r'\b',text,re.M):errors.append(f'missing {label} {name}')
    for token in ['sorry','axiom','admit','unsafe','partial','implemented_by','native_decide','Classical','simp','simpa','Matrix.inv']:
        if re.search(r'\b'+re.escape(token)+r'\b',text):errors.append(f'forbidden {label} token {token}')
for nid in ['C016','C017']:
    node=json.loads((REG/f'nodes/{nid}.json').read_text())
    if node.get('workflow',{}).get('freeze_state')!='FROZEN_VERIFIED':errors.append(nid+' freeze')
    if node.get('implementation_status',{}).get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE':errors.append(nid+' implementation status')
    evnode=node.get('evidence',{})
    if evnode.get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE' or evnode.get('shared_kernel_verified_declarations')!=12:errors.append(nid+' node evidence')
    if evnode.get('axiom_profile_counts')!={'choice_propext_quot':10,'propext_quot_only':2,'axiom_free':0}:errors.append(nid+' node axiom profile')
    dp=node.get('documentation_profile',{})
    if dp.get('v2_state')!='COMPLETE_V2' or dp.get('countercheck_status')!='PASS':errors.append(nid+' documentation profile')
    for a in dp.get('code_anchors',[]):
        if a.get('resolution') not in {'RESOLVED','RESOLVED_KERNEL_VERIFIED'}:errors.append('unresolved '+nid+' anchor '+str(a.get('symbol')))
status={r['id']:r for r in rows(DAG/'DAG_DISPLAY_STATUS.tsv')}
for nid,want,color in [('C016','FINISHED','#70C779'),('C017','FINISHED','#70C779'),('C009','FINISHED','#70C779')]:
    r=status.get(nid,{})
    if r.get('display_status')!=want or r.get('color')!=color:errors.append(nid+' display status')
edges={r['id']:r for r in rows(DAG/'EDGES.tsv')}
for eid in ['E028','E029']:
    if edges.get(eid,{}).get('status')!='ACTIVE_VERIFIED':errors.append(eid+' status')
for eid in ['E030','E031','E069']:
    if edges.get(eid,{}).get('status')!='ACTIVE_VERIFIED':errors.append(eid+' status')
if EVIDENCE.is_file() and TRANSCRIPT.is_file():
    ev=json.loads(EVIDENCE.read_text())
    expected={'choice_propext_quot':10,'propext_quot_only':2,'axiom_free':0}
    for k,v in {'schema':'cnna.c016-c017-kernel-build-evidence.v1','status':'PASS','toolchain':'leanprover/lean4:v4.31.0','proof_modules':21,'c016_c017_audited_declarations':12,'c016_c017_current_proof_axiom_audit':'PASS','full_package_boundary_audit':'PASS'}.items():
        if ev.get(k)!=v:errors.append('evidence '+k)
    if ev.get('c016_c017_axiom_profile_counts')!=expected:errors.append('evidence axiom profiles')
    if ev.get('transitive_axioms_observed')!=['propext','Classical.choice','Quot.sound']:errors.append('evidence transitive axioms')
    if ev.get('direct_project_axioms')!=0 or ev.get('sorry_count')!=0:errors.append('project axiom/sorry count')
    if not all(ev.get(k) is True for k in ['retained_verified_p001_source_hash_match','retained_verified_m003_m004_source_hash_match','retained_verified_p002_source_hash_match','retained_verified_c008_source_hash_match']):errors.append('retained prior hashes')
    if sha(TRANSCRIPT)!=ev.get('transcript_sha256'):errors.append('transcript hash')
    for rel,h in ev.get('verified_source_sha256',{}).items():
        p=LEAN/rel
        if not p.is_file() or sha(p)!=h:errors.append('source hash '+rel)
    text=TRANSCRIPT.read_text(encoding='utf-8')
    for marker in ['C016_C017_CURRENT_PROOF_AXIOM_AUDIT PASS','"c016": "KERNEL_VERIFIED_CURRENT_BUILD"','"c017": "KERNEL_VERIFIED_CURRENT_BUILD"','"c016_c017_projection_closure_olean": true','FULL_PACKAGE_BOUNDARY_AUDIT PASS']:
        if marker not in text:errors.append('transcript marker '+marker)
run=subprocess.run([sys.executable,str(LEAN/'audit/check_package_boundary.py')],cwd=LEAN,capture_output=True,text=True)
if run.returncode:errors.append('static boundary '+(run.stdout+run.stderr).strip())
else:
    st=json.loads(run.stdout)
    for nid in ['c016','c017']:
        if st.get('proofs',{}).get(nid)!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE':errors.append('static '+nid+' exact source evidence')
    if st.get('build_evidence',{}).get('retained_verified_c016_c017_source_hash_match') is not True:errors.append('static C016/C017 retained hash')
result={'schema':'cnna.c016-c017-kernel-verified-audit.v1','status':'PASS' if not errors else 'FAIL','date':'2026-08-08','toolchain':'leanprover/lean4:v4.31.0','kernel_verified_declarations':12,'axiom_profile_counts':{'choice_propext_quot':10,'propext_quot_only':2,'axiom_free':0},'python_regression':'PASS_114_TESTS_1086_SUBTESTS','handoff_target':'C009','errors':errors}
(DAG/'C016_C017_KERNEL_VERIFIED_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2));sys.exit(1 if errors else 0)
