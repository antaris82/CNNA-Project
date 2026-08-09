#!/usr/bin/env python3
from __future__ import annotations
from collections import Counter
from pathlib import Path
import csv,hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[3]
TOOLS=ROOT/'derivation/registry/tools'
def rows(p):
 with p.open(encoding='utf-8',newline='') as f:return list(csv.DictReader(f,delimiter='\t'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]
checks=[
 ('D0','validate_d0.py'),('D0 traceability','validate_d0_traceability.py'),('D2 structural','validate_d2_structural.py'),
 ('G0','validate_g0.py'),('G1','validate_g1.py'),('G2','validate_g2.py'),
 ('external references','validate_external_references.py'),('CNNA architecture','validate_cnna_architecture_identity.py'),('open provenance','validate_open_provenance_integration.py'),('P001','validate_p001_kernel_verified.py'),
 ('M003/M004','validate_m003_m004_kernel_verified.py'),('P002','validate_p002_kernel_verified.py'),('C008','validate_c008_kernel_verified.py'),('C016/C017','validate_c016_c017_kernel_verified.py'),('C009','validate_c009_kernel_verified.py'),('T002','validate_t002_kernel_verified.py')]
for label,script in checks:
 run=subprocess.run([sys.executable,str(TOOLS/script)],cwd=ROOT,capture_output=True,text=True)
 if run.returncode:errors.append(label+': '+(run.stdout+run.stderr).strip())
nodes=rows(ROOT/'derivation/registry/dag/NODES.tsv');edges=rows(ROOT/'derivation/registry/dag/EDGES.tsv');display=rows(ROOT/'derivation/registry/dag/DAG_DISPLAY_STATUS.tsv')
if len(nodes)!=145 or len(edges)!=401:errors.append('DAG cardinality')
expected=Counter({'FINISHED':31,'UNFINISHED':113,'ACTIVE':1})
if Counter(r['display_status'] for r in display)!=expected:errors.append('DAG display status counts')
state=json.loads((ROOT/'CURRENT_STATE.json').read_text());validation=json.loads((ROOT/'VALIDATION.json').read_text())
if state.get('dag',{}).get('current_node')!='T003':errors.append('CURRENT_STATE current node')
if state.get('p001',{}).get('kernel_verified_declarations')!=142:errors.append('CURRENT_STATE P001')
if state.get('m003_m004',{}).get('kernel_verified_declarations')!=11:errors.append('CURRENT_STATE M003/M004')
p2=state.get('p002',{})
if p2.get('public_declarations')!=6 or p2.get('kernel_verified_declarations')!=6 or p2.get('status')!='KERNEL_VERIFIED_AXIOM_FREE':errors.append('CURRENT_STATE P002')
c8=state.get('c008',{})
if c8.get('public_declarations')!=7 or c8.get('kernel_verified_declarations')!=7 or c8.get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE':errors.append('CURRENT_STATE C008')

c16c17=state.get('c016_c017',{})
if c16c17.get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE' or c16c17.get('audited_declarations')!=12 or c16c17.get('kernel_verified_declarations')!=12:errors.append('CURRENT_STATE C016/C017 kernel gate')
for nid in ['C016','C017']:
 nd=json.loads((ROOT/f'derivation/registry/nodes/{nid}.json').read_text())
 if nd.get('implementation_status',{}).get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE':errors.append(f'{nid} kernel-verified status')
c9=json.loads((ROOT/'derivation/registry/nodes/C009.json').read_text())
if c9.get('implementation_status',{}).get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE':errors.append('C009 kernel-verified status')
if state.get('c009',{}).get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE' or state.get('c009',{}).get('kernel_verified_declarations')!=8:errors.append('CURRENT_STATE C009 kernel gate')
t2=json.loads((ROOT/'derivation/registry/nodes/T002.json').read_text())
if t2.get('implementation_status',{}).get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE' or t2.get('implementation_status',{}).get('kernel_verified_declarations')!=26:errors.append('T002 kernel-verified status')
if state.get('t002',{}).get('status')!='KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE' or state.get('t002',{}).get('kernel_verified_declarations')!=26:errors.append('CURRENT_STATE T002 kernel gate')
lean=validation.get('lean',{})
if (lean.get('current_source_modules')!=25 or lean.get('latest_kernel_verified_source_modules')!=25 or lean.get('p002_declarations')!=6 or lean.get('p002_kernel_verified_declarations')!=6 or lean.get('p002_unverified_declarations')!=0 or lean.get('c008_declarations')!=7 or lean.get('c008_kernel_verified_declarations')!=7 or lean.get('c008_unverified_declarations')!=0 or lean.get('c016_c017_declarations_planned')!=12 or lean.get('c016_c017_kernel_verified_declarations')!=12 or lean.get('c016_c017_unverified_declarations')!=0 or lean.get('c016_c017_axiom_audit')!='PASS_12_OF_12' or lean.get('c009_declarations_planned')!=8 or lean.get('c009_kernel_verified_declarations')!=8 or lean.get('c009_unverified_declarations')!=0 or lean.get('c009_axiom_audit')!='PASS_8_OF_8' or lean.get('t002_declarations_planned')!=26 or lean.get('t002_kernel_verified_declarations')!=26 or lean.get('t002_unverified_declarations')!=0 or lean.get('t002_axiom_audit')!='PASS_26_OF_26'):errors.append('VALIDATION Lean source/build scope')
# Explicit implementation status on every proof node.
for node in (ROOT/'derivation/registry/nodes').glob('P*.json'):
 d=json.loads(node.read_text())
 if not d.get('implementation_status',{}).get('status'):errors.append('missing proof implementation_status '+node.stem)
# PDF and binding integrity.
main=ROOT/'derivation/paper/main/paper.pdf';supp=ROOT/'derivation/supplement/supplementary.pdf'
if not main.is_file() or not supp.is_file():errors.append('PDF missing')
else:
 for doc in [state.get('documentation',{}),validation.get('documentation',{})]:
  if doc.get('main_paper_pdf_sha256')!=sha(main):errors.append('main PDF hash')
  if doc.get('supplementary_pdf_sha256')!=sha(supp):errors.append('supplement PDF hash')
 binding=(ROOT/'derivation/supplement/MAIN_PAPER_SHA256.txt').read_text().split()[0]
 if binding!=sha(main):errors.append('supplement-to-main hash binding')
# No generated caches/intermediates in deliverable tree.
for path in ROOT.rglob('*'):
 if path.is_dir() and path.name in {'__pycache__','.pytest_cache'}:errors.append('cache directory '+str(path.relative_to(ROOT)))
 if path.is_file() and (path.suffix in {'.pyc','.pyo'} or path.name=='.coverage'):errors.append('cache file '+str(path.relative_to(ROOT)))
for directory,stem in [(ROOT/'derivation/paper/main','paper'),(ROOT/'derivation/supplement','supplementary')]:
 for suffix in ['aux','bbl','bcf','blg','fdb_latexmk','fls','log','out','run.xml','xdv']:
  if (directory/f'{stem}.{suffix}').exists():errors.append('LaTeX intermediate '+suffix)
if errors:
 print('\n'.join('FAIL '+e for e in errors));sys.exit(1)
result={'nodes':145,'edges':401,'display_status_counts':dict(expected),'p001_kernel_verified_declarations':142,'m003_m004_kernel_verified_declarations':11,'p002_source_declarations':6,'p002_kernel_verified_declarations':6,'c008_kernel_verified_declarations':7,'current_source_modules':25,'latest_kernel_verified_source_modules':25,'c016_c017_source_declarations':12,'c016_c017_kernel_verified_declarations':12,'c009_source_declarations':8,'c009_kernel_verified_declarations':8,'t002_source_declarations':26,'t002_kernel_verified_declarations':26,'external_reference_uses_unique':61,'cnna_architecture_map_entries':27,'open_provenance_map_entries':74}
print('CURRENT_STATE_VALIDATION PASS');print(json.dumps(result,indent=2))
