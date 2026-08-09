#!/usr/bin/env python3
from pathlib import Path
import csv, hashlib, json, re, sys

ROOT = Path(__file__).resolve().parents[3]
REG = ROOT / "derivation/registry"
DOC = REG / "documentation"
DAG = REG / "dag"
TARGETS = ["I001", "I002", "C001", "C002", "C003"]
EXPECTED_NUMBERS = ["001", "002", "003", "004", "005"]
EXPECTED_TIERS = {"I001":"D0", "I002":"D0", "C001":"D0", "C002":"D1", "C003":"D1"}
STRUCTURAL = ["C002", "C003"]
REQUIRED_D1_SUPP = [
    "Position In Derivation", "Mathematical Contract", "Introduction Reason",
    "Explicit Construction", "Invariants", "Canonicity Or Uniqueness",
    "Boundary Cases", "Python Lean Cross Layer", "Countercheck", "Result",
    "Downstream Handoff", "Code Anchors",
]
REQUIRED_MAIN = [
    "Position and scientific role.", "Mathematical contract.",
    "Result and handoff.", "Primary code anchors.",
]

def rows(path: Path):
    with path.open(encoding="utf-8", newline="") as h:
        return list(csv.DictReader(h, delimiter="\t"))

def sha(path: Path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

errors=[]
nodes={r['id']:r for r in rows(DAG/'NODES.tsv')}
tiers={r['id']:r for r in rows(DOC/'DOCUMENTATION_TIERS.tsv')}
coverage={r['id']:r for r in rows(DOC/'DOCUMENTATION_COVERAGE.tsv')}
anchors=rows(DOC/'CODE_ANCHORS.tsv')
if [nodes[s]['node_number'] for s in TARGETS] != EXPECTED_NUMBERS:
    errors.append('canonical order mismatch for 001-005')

for sid in TARGETS:
    if nodes[sid].get('documentation_v2_state') != 'COMPLETE_V2': errors.append('NODES state '+sid)
    if tiers[sid].get('documentation_v2_state') != 'COMPLETE_V2': errors.append('TIERS state '+sid)
    if coverage[sid].get('documentation_v2_state') != 'COMPLETE_V2': errors.append('COVERAGE state '+sid)
    if nodes[sid].get('countercheck_status') != 'PASS' or coverage[sid].get('countercheck_status') != 'PASS': errors.append('countercheck '+sid)
    p=REG/'nodes'/f'{sid}.json'; d=json.loads(p.read_text(encoding='utf-8')); prof=d.get('documentation_profile',{})
    if prof.get('tier') != EXPECTED_TIERS[sid] or prof.get('v2_state') != 'COMPLETE_V2': errors.append('profile '+sid)
    if prof.get('countercheck_status') != 'PASS' or prof.get('freeze_revalidation_required') is not False: errors.append('profile gate '+sid)
    main=ROOT/d['section_hierarchy']['main_artifact']; supp=ROOT/d['section_hierarchy']['supplement_artifact']
    if not main.is_file() or not supp.is_file(): errors.append('artifact missing '+sid); continue
    mt=main.read_text(encoding='utf-8'); st=supp.read_text(encoding='utf-8')
    if f"\\cnnaNodeHeading{{{d['node_number']}}}{{{sid}}}" not in mt: errors.append('stable heading '+sid)
    if 'REQUIRED_CONTENT_PENDING' in mt or 'REQUIRED_CONTENT_PENDING' in st: errors.append('pending marker '+sid)
    if d.get('artifacts',{}).get('math_prose') != sha(main): errors.append('main hash '+sid)
    if d.get('artifacts',{}).get('supplement_documentation') != sha(supp): errors.append('supp hash '+sid)
    ce=prof.get('completion_evidence',{})
    if ce.get('main_sha256') != sha(main) or ce.get('supplement_sha256') != sha(supp): errors.append('completion hash '+sid)
    node_anchors=[a for a in anchors if a['id']==sid]
    if not node_anchors: errors.append('no anchors '+sid)
    layers={a['layer'] for a in node_anchors}
    if not {'python','python_test','lean_core'}.issubset(layers): errors.append('anchor layers '+sid)
    for a in node_anchors:
        ap=ROOT/a['path']
        if not ap.is_file() or sha(ap)!=a['source_sha256']: errors.append('anchor integrity '+sid+':'+a['symbol'])
    if sid in STRUCTURAL:
        for marker in REQUIRED_MAIN:
            if marker not in mt: errors.append(f'main marker {sid}: {marker}')
        for heading in REQUIRED_D1_SUPP:
            if not re.search(rf'^## {re.escape(heading)}\s*$', st, flags=re.M): errors.append(f'supp heading {sid}: {heading}')

# Node-specific load-bearing documentation checks.
c002=(ROOT/json.loads((REG/'nodes/C002.json').read_text())['section_hierarchy']['supplement_artifact']).read_text()
for term in ['rootGenesis_eqCanonical','rootHasNoParent','rootHasNoGeometricPosition','test_c002_does_not_smuggle_downstream_metadata']:
    if term not in c002: errors.append('C002 dossier term '+term)
c003=(ROOT/json.loads((REG/'nodes/C003.json').read_text())['section_hierarchy']['supplement_artifact']).read_text()
for term in ['unsnoc?_snoc','snoc_parent_unique','snoc_slot_unique','BoundedProvenanceAddress.child','test_zero_cutoff_is_root_only_for_admitted_words']:
    if term not in c003: errors.append('C003 dossier term '+term)

result={
 'schema':'cnna.d2-structural-documentation-audit.v1',
 'status':'PASS' if not errors else 'FAIL',
 'documentation_tier_audit':'D2',
 'documented_nodes':TARGETS,
 'structural_nodes':STRUCTURAL,
 'canonical_range':'001-005',
 'complete_v2_nodes':sum(r['documentation_v2_state']=='COMPLETE_V2' for r in nodes.values()),
 'migration_required_nodes':sum(r['documentation_v2_state']=='V1_CONTENT_PRESENT_MIGRATION_REQUIRED' for r in nodes.values()),
 'not_started_nodes':sum(r['documentation_v2_state']=='NOT_STARTED' for r in nodes.values()),
 'source_code_modified':False,
 'errors':errors,
}
(DOC/'D2_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
sys.exit(1 if errors else 0)
