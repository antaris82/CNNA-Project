#!/usr/bin/env python3
from pathlib import Path
import csv,hashlib,json,re,sys
ROOT=Path(__file__).resolve().parents[3]
DAG=ROOT/'derivation/registry/dag'; LEAN=ROOT/'derivation/code/lean'
SRC=LEAN/'proofs/src/CNNAProofs/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S01_PrimitiveInputsGrammarAndEventOrder/S06_C018_CanonicalBfsLexicographicProvenanceBirthSchedule/Proofs/S01_P002_CanonicalScheduleStrictTotalOrderClosure.lean'
EVIDENCE=LEAN/'audit/evidence/USER_LOCAL_P002_FULL_BUILD_20260808.json'
TRANSCRIPT=LEAN/'audit/evidence/USER_LOCAL_P002_FULL_BUILD_20260808.txt'
def rows(p):
 with p.open(encoding='utf-8',newline='') as f:return list(csv.DictReader(f,delimiter='\t'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]; text=SRC.read_text(encoding='utf-8') if SRC.is_file() else ''
required=['CanonicalScheduleStrictTotalOrderClosure','canonicalScheduleStrictTotalOrderClosure','IsMinimalSelectedChild','minimalSelectedChild_unique','CanonicalScheduleStrictTotalOrderContract','canonicalScheduleStrictTotalOrderContract']
for name in required:
 if not re.search(r'^(?:structure|def|theorem)\s+'+re.escape(name)+r'\b',text,re.M):errors.append('missing '+name)
for token in ['ResponseCapableState','Unsaturated','bornNonRoot','nextOpen','native_decide','noncomputable','Classical','simp','simpa','sorry','axiom','admit']:
 if re.search(r'\b'+re.escape(token)+r'\b',text):errors.append('forbidden token '+token)
node=json.loads((ROOT/'derivation/registry/nodes/P002.json').read_text())
if node.get('evidence',{}).get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE':errors.append('P002 evidence status')
if node.get('evidence',{}).get('public_declarations')!=6 or node.get('evidence',{}).get('kernel_verified_declarations')!=6:errors.append('P002 declaration counts')
if node.get('evidence',{}).get('axiom_audit')!='PASS_AXIOM_FREE_6_OF_6' or node.get('evidence',{}).get('proof_gate_closed') is not True:errors.append('P002 axiom/proof gate')
if node.get('implementation_status',{}).get('status')!='KERNEL_VERIFIED':errors.append('P002 implementation status')
for anchor in node.get('documentation_profile',{}).get('code_anchors',[]):
 if anchor.get('resolution')!='RESOLVED_KERNEL_VERIFIED':errors.append('P002 anchor not kernel verified '+str(anchor.get('symbol')))
status={r['id']:r for r in rows(DAG/'DAG_DISPLAY_STATUS.tsv')}
for nid,want,color in [('P002','FINISHED','#70C779'),('C018','FINISHED','#70C779')]:
 row=status.get(nid,{})
 if row.get('display_status')!=want or row.get('color')!=color:errors.append(nid+' display status')
edges=rows(DAG/'EDGES.tsv')
if any(e['source']=='P002' and e['target']=='P003' for e in edges):errors.append('obsolete P002->P003 edge')
if not EVIDENCE.is_file() or not TRANSCRIPT.is_file():errors.append('P002 retained build evidence missing')
else:
 ev=json.loads(EVIDENCE.read_text())
 if ev.get('schema')!='cnna.p002-kernel-build-evidence.v1' or ev.get('status')!='PASS':errors.append('P002 build evidence schema/status')
 if ev.get('toolchain')!='leanprover/lean4:v4.31.0' or ev.get('proof_modules')!=17 or ev.get('p002_proof_declarations')!=6:errors.append('P002 build evidence scope')
 if ev.get('p002_axiom_profile_counts')!={'choice_propext_quot':0,'propext_quot_only':0,'axiom_free':6} or ev.get('transitive_axioms_observed')!=[]:errors.append('P002 axiom profile')
 if ev.get('p002_current_proof_axiom_audit')!='PASS' or ev.get('full_package_boundary_audit')!='PASS':errors.append('P002 audit evidence')
 if ev.get('retained_verified_p001_source_hash_match') is not True or ev.get('retained_verified_m003_m004_source_hash_match') is not True:errors.append('retained prior proof hashes')
 if sha(TRANSCRIPT)!=ev.get('transcript_sha256'):errors.append('P002 transcript hash')
 for rel,expected in ev.get('verified_source_sha256',{}).items():
  p=LEAN/rel
  if not p.is_file() or sha(p)!=expected:errors.append('P002 source hash '+rel)
 transcript=TRANSCRIPT.read_text(encoding='utf-8')
 for marker in ['P002_CURRENT_PROOF_AXIOM_AUDIT PASS','"p002_static_order_closure_olean": true','FULL_PACKAGE_BOUNDARY_AUDIT PASS']:
  if marker not in transcript:errors.append('transcript marker '+marker)
result={'schema':'cnna.p002-kernel-verified-audit.v1','status':'PASS' if not errors else 'FAIL','public_declarations':6,'kernel_verified_declarations':6,'axiom_free_declarations':6,'dynamic_scope_owner':'C004','downstream_c008_status':status.get('C008',{}).get('display_status'),'errors':errors}
(DAG/'P002_KERNEL_VERIFIED_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2));sys.exit(1 if errors else 0)
