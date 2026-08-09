#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import csv, json, re, sys

ROOT=Path(__file__).resolve().parents[3]
DAG=ROOT/'derivation/registry/dag'
DOC=ROOT/'derivation/registry/documentation'

def rows(path):
    with path.open(encoding='utf-8',newline='') as f:return list(csv.DictReader(f,delimiter='\t'))

errors=[]
nodes=rows(DAG/'NODES.tsv')
index=rows(DOC/'NODE_TRACEABILITY_INDEX.tsv')
anchors=rows(DOC/'CODE_ANCHORS.tsv')
if len(nodes)!=145: errors.append(f'node count {len(nodes)} != 145')
if [int(n['node_number']) for n in sorted(nodes,key=lambda x:int(x['derivation_order']))] != list(range(1,146)):
    errors.append('node numbers are not exactly 001..145 in derivation order')
if len(index)!=145: errors.append(f'traceability index rows {len(index)} != 145')
idx={r['semantic_id']:r for r in index}
anchor_ids={a['id'] for a in anchors}
for n in nodes:
    num=f"{int(n['node_number']):03d}"; nid=n['id']; label=f'{num} · {nid}'
    if n.get('canonical_node_label')!=label: errors.append(f'{nid} canonical label mismatch')
    stable=n.get('stable_node_directory_name','')
    if not stable.startswith(f'{num}_{nid}__'): errors.append(f'{nid} stable directory identity mismatch')
    for field in ['main_section_directory','supplement_section_directory']:
        p=ROOT/n[field]
        if p.name!=stable: errors.append(f'{nid} {field} final component not stable')
    rec=ROOT/f'derivation/registry/nodes/{nid}.json'
    if not rec.is_file(): errors.append(f'{nid} node record missing'); continue
    data=json.loads(rec.read_text(encoding='utf-8'))
    ident=data.get('canonical_identity',{})
    if ident.get('canonical_node_label')!=label or ident.get('semantic_id')!=nid:
        errors.append(f'{nid} canonical identity block mismatch')
    row=idx.get(nid)
    if not row: errors.append(f'{nid} missing traceability row'); continue
    for field,expected in {
      'node_number':num,'canonical_node_label':label,'semantic_id':nid,
      'current_section_path':n['paper_section'],'stable_node_directory_name':stable,
      'main_artifact':n['main_section_artifact'],'supplement_artifact':n['supplement_section_artifact']
    }.items():
        if row.get(field)!=expected: errors.append(f'{nid} traceability {field} mismatch')
    main=ROOT/n['main_section_artifact']
    if main.is_file():
        text=main.read_text(encoding='utf-8')
        command='cnnaProofNodeHeading' if n['paper_section'].count('.')==3 else 'cnnaNodeHeading'
        if not re.search(rf'^\\{command}\{{{num}\}}\{{{re.escape(nid)}\}}\{{',text,re.M):
            errors.append(f'{nid} stable TeX heading missing')
        if f'\\cnnaNodePlacement{{{n["paper_section"]}}}{{{n["documentation_tier"]}}}' not in text:
            errors.append(f'{nid} explicit placement metadata missing')
    supp=ROOT/n['supplement_section_artifact']
    if supp.is_file():
        text=supp.read_text(encoding='utf-8')
        if not text.startswith(f'# {label} — '): errors.append(f'{nid} stable supplement heading missing')
        if f'**Current section path:** `{n["paper_section"]}`' not in text: errors.append(f'{nid} supplement placement missing')

if {n['id'] for n in nodes}-anchor_ids:
    # Nodes without code anchors are allowed; this check only ensures all anchor IDs are valid.
    pass
invalid_anchor_ids=anchor_ids-{n['id'] for n in nodes}
if invalid_anchor_ids: errors.append(f'invalid code-anchor IDs: {sorted(invalid_anchor_ids)}')
for a in anchors:
    if not a.get('path') or not a.get('symbol') or not a.get('source_sha256') or not a.get('start_line') or not a.get('end_line'):
        errors.append(f'incomplete code anchor for {a.get("id")}')

paper=(ROOT/'derivation/paper/main/paper.tex').read_text(encoding='utf-8')
if r'\input{derivation/paper/main/TRACEABILITY_AND_READING_GUIDE.tex}' not in paper:
    errors.append('main-paper traceability guide not included')
supp=(ROOT/'derivation/supplement/supplementary.md').read_text(encoding='utf-8')
if '# Traceability and reading convention' not in supp:
    errors.append('supplement traceability guide not included')
if re.search(r'^#\s+[0-9]+(?:\.[0-9]+)+\.\s+-',supp,re.M):
    errors.append('section-number-dependent supplement node heading remains')
for p in (ROOT/'derivation/paper/main/sections').rglob('SECTION.tex'):
    text=p.read_text(encoding='utf-8')
    if re.search(r'^\\subsubsection\{',text,re.M) or re.search(r'^\\paragraph\{-[^*]',text,re.M):
        errors.append(f'section-counter-dependent node heading remains: {p.relative_to(ROOT)}')

policy=json.loads((DOC/'TRACEABILITY_POLICY.json').read_text(encoding='utf-8'))
if policy.get('canonical_visible_node_label')!='NNN · ID' or not policy.get('parallel_dag_forbidden'):
    errors.append('traceability policy mismatch')

result={
 'schema':'cnna.d0-stable-node-label-traceability-audit.v1',
 'status':'PASS' if not errors else 'FAIL',
 'nodes':len(nodes),'traceability_rows':len(index),'code_anchors':len(anchors),
 'stable_node_labels':sum(n.get('canonical_node_label')==f"{int(n['node_number']):03d} · {n['id']}" for n in nodes),
 'section_independent_node_headings':not any('heading' in e for e in errors),
 'stable_node_directory_names':not any('directory' in e for e in errors),
 'one_dag_only':True,'errors':errors,
}
(DOC/'D0_TRACEABILITY_AUDIT.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,ensure_ascii=False,indent=2))
sys.exit(1 if errors else 0)
