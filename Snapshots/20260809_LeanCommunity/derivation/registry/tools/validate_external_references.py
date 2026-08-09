#!/usr/bin/env python3
from pathlib import Path
from collections import Counter
import csv,json,sys
ROOT=Path(__file__).resolve().parents[3]
REF=ROOT/'derivation/registry/references'
def rows(p):
 with p.open(encoding='utf-8',newline='') as f:return list(csv.DictReader(f,delimiter='\t'))
refs=rows(REF/'EXTERNAL_REFERENCES.tsv'); uses=rows(REF/'EXTERNAL_REFERENCE_USAGE.tsv'); assertions=rows(REF/'EXTERNAL_REFERENCE_ASSERTIONS.tsv')
known={r['reference_id'] for r in refs}; errors=[]
if len(known)!=len(refs):errors.append('duplicate reference_id')
seen=Counter((u['target_file'],u['anchor_id']) for u in uses)
for pair,count in seen.items():
 if count!=1:errors.append('nonunique target/anchor '+repr(pair))
for u in uses:
 if u['reference_id'] not in known:errors.append('unknown usage reference '+u['usage_id'])
 target=ROOT/u['target_file']
 if not target.is_file():errors.append('missing target '+u['usage_id']+' '+u['target_file']);continue
 text=target.read_text(encoding='utf-8')
 if u['scope']=='MAIN_TEX':
  begin='% CNNA-EXTREF-BEGIN '+u['usage_id']; end='% CNNA-EXTREF-END '+u['usage_id']
 else:
  begin='<!-- CNNA-EXTREF-BEGIN '+u['usage_id']+' -->'; end='<!-- CNNA-EXTREF-END '+u['usage_id']+' -->'
 if text.count(begin)!=1 or text.count(end)!=1:errors.append('marker multiplicity '+u['usage_id'])
for a in assertions:
 if a['reference_id'] not in known:errors.append('unknown assertion reference '+a.get('assertion_id',''))
result={'schema':'cnna.external-reference-audit.v1','status':'PASS' if not errors else 'FAIL','references':len(refs),'uses':len(uses),'assertions':len(assertions),'unique_target_anchor_pairs':len(seen),'errors':errors}
(REF/'EXTERNAL_REFERENCE_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2));sys.exit(1 if errors else 0)
