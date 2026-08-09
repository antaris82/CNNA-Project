#!/usr/bin/env python3
from pathlib import Path
import csv,json,re,sys
ROOT=Path(__file__).resolve().parents[3]
errors=[]
def rows(p):
 with p.open(encoding='utf-8',newline='') as f:return list(csv.DictReader(f,delimiter='\t'))
identity=json.loads((ROOT/'PROJECT_IDENTITY.json').read_text())
if identity.get('acronym_expansion')!='ComplemeNt Net Architecture':errors.append('project identity expansion')
if 'cut-, scale-, or projection-relative' not in identity.get('complement_guard',''):errors.append('relative complement guard')
main=(ROOT/'derivation/paper/main/paper.tex').read_text()
if 'CNNA_ARCHITECTURE_CONCEPT.tex' not in main:errors.append('main-paper input')
concept=(ROOT/'derivation/paper/main/CNNA_ARCHITECTURE_CONCEPT.tex').read_text()
for phrase in ['ComplemeNt Net Architecture','C001 fixes the empty baseline','Complement is a relative role','does not promote']:
 if phrase not in concept:errors.append('main concept phrase '+phrase)
supp=(ROOT/'derivation/supplement/supplementary.md').read_text()
if 'CNNA-ARCHITECTURE-BEGIN SUPPLEMENT' not in supp:errors.append('supplement identity section')
required_early={'C001','C002','C003','C004A','C013','C014'}
for nid in required_early:
 d=json.loads((ROOT/f'derivation/registry/nodes/{nid}.json').read_text())
 if not d.get('cnna_architecture_context'):errors.append('node context '+nid)
 for key in ('main_artifact','supplement_artifact'):
  text=(ROOT/d['section_hierarchy'][key]).read_text()
  if f'CNNA-ARCHITECTURE-BEGIN {nid}' not in text:errors.append('node prose '+nid+' '+key)
map_rows=rows(ROOT/'derivation/registry/OPEN_PROVENANCE_NODE_MAP.tsv')
cnna=[r for r in map_rows if r['concept_id']=='CNNA-00']
if len(cnna)<20:errors.append('throughline map too small')
for r in cnna:
 d=json.loads((ROOT/f"derivation/registry/nodes/{r['node_id']}.json").read_text())
 if d.get('cnna_architecture_context',{}).get('role')!=r['node_role']:errors.append('map/node mismatch '+r['node_id'])
graph=(ROOT/'derivation/registry/dag/DAG_yEd.graphml').read_text()
if graph.count('CNNA architecture role:') < len(cnna):errors.append('graph descriptions')
if errors:
 print('\n'.join('FAIL '+e for e in errors));sys.exit(1)
result={'schema':'cnna.architecture-identity-audit.v1','status':'PASS','throughline_entries':len(cnna),'early_prose_nodes':len(required_early),'name':'ComplemeNt Net Architecture'}
(ROOT/'derivation/registry/documentation/CNNA_ARCHITECTURE_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
