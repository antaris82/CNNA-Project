#!/usr/bin/env python3
from pathlib import Path
import csv,json,re,collections,xml.etree.ElementTree as ET,sys
ROOT=Path(__file__).resolve().parents[3];DAG=ROOT/'derivation/registry/dag'
def rows(p):
 with p.open(encoding='utf-8',newline='') as f:return list(csv.DictReader(f,delimiter='\t'))
def sk(s):return tuple(map(int,s.split('.')))
errors=[];N=rows(DAG/'NODES.tsv');E=rows(DAG/'EDGES.tsv');R=rows(DAG/'DAG_ROOTS.tsv')
ids=[n['id'] for n in N];idset=set(ids)
if len(N)!=145:errors.append(f'nodes={len(N)}')
if len(E)!=401:errors.append(f'edges={len(E)}')
if len(idset)!=145:errors.append('duplicate node IDs')
legacy_dash='SO'+'LL-'
if any(i.startswith(legacy_dash) for i in ids):errors.append('prefixed current node ID')
if [n['node_number'] for n in N] != [f'{i:03d}' for i in range(1,146)]:errors.append('node numbering')
if [int(n['derivation_order']) for n in N] != list(range(1,146)):errors.append('derivation order')
if any(not n['paper_section'] or not n['derivation_rank'] for n in N):errors.append('missing section/rank')
if len({n['paper_section'] for n in N})!=145:errors.append('paper sections not unique')
if sum(i.startswith('P') for i in ids)!=59:errors.append('proof count')
for e in E:
 if e['source'] not in idset or e['target'] not in idset:errors.append(f'dangling edge {e["id"]}')
nd={n['id']:n for n in N}
# Full graph acyclicity
ind={i:0 for i in ids};out=collections.defaultdict(list);und=collections.defaultdict(set)
for e in E:ind[e['target']]+=1;out[e['source']].append(e['target']);und[e['source']].add(e['target']);und[e['target']].add(e['source'])
q=collections.deque([i for i,d in ind.items() if d==0]);seen=[]
while q:
 u=q.popleft();seen.append(u)
 for v in out[u]:ind[v]-=1;q.append(v) if ind[v]==0 else None
if len(seen)!=145:errors.append('cycle')
# Weak connectivity
reach=set();q=collections.deque([ids[0]])
while q:
 u=q.popleft()
 if u in reach:continue
 reach.add(u);q.extend(und[u]-reach)
if len(reach)!=145:errors.append(f'weak component coverage={len(reach)}')
actual_roots={i for i in ids if not any(e['target']==i for e in E)}
registered={r['id'] for r in R}
if actual_roots!=registered:errors.append('root registry mismatch')
visible={r['id'] for r in R if r['top_visible']=='true'}
if visible!={'I001','I002','C001'}:errors.append(f'top visible roots={sorted(visible)}')
if any(int(nd[i]['derivation_rank'])!=0 for i in visible):errors.append('visible root rank')
if any(int(nd[i]['derivation_rank'])==0 for i in idset-visible):errors.append('non-origin rank zero')
# Hard dependencies must move forward in order, rank, and section. Certification edges are explicitly non-hard.
for e in E:
 if e['edge_class']=='PROOF_CERTIFICATION' and (e['hard_dependency']!='false' or e['layout_constraint']!='false'):errors.append(f'certification classification {e["id"]}')
 if e['hard_dependency']=='true':
  a,b=nd[e['source']],nd[e['target']]
  if int(a['derivation_order'])>=int(b['derivation_order']):errors.append(f'backward order {e["id"]}')
  if int(a['derivation_rank'])>=int(b['derivation_rank']):errors.append(f'backward rank {e["id"]}')
  if sk(a['paper_section'])>=sk(b['paper_section']):errors.append(f'backward section {e["id"]}')
if sum(e['edge_class']=='PROOF_CERTIFICATION' for e in E)!=59:errors.append('proof-certification count')
if sum(e['hard_dependency']=='true' for e in E)!=342:errors.append('hard-edge count')
# One canonical representation, no old parallel DAG files.
legacy_prefix='SO'+'LL'
for old in [legacy_prefix+'_NODES.tsv',legacy_prefix+'_EDGES.tsv',legacy_prefix+'_DAG_yEd.graphml']:
 if (DAG/old).exists():errors.append(f'legacy parallel file {old}')
if len(list(DAG.glob('*.graphml')))!=1:errors.append('parallel GraphML files')
# GraphML semantic labels in the editor-owned yEd Live layout.
g=DAG/'DAG_yEd.graphml';tree=ET.parse(g)
ns={'g':'http://graphml.graphdrawing.org/xmlns','y':'http://www.yworks.com/xml/yfiles-common/3.0'}
gnodes=tree.findall('.//g:node',ns);gedges=tree.findall('.//g:edge',ns)
if len(gnodes)!=145 or len(gedges)!=401:errors.append('GraphML size')
semantic_labels={}
for x in gnodes:
 texts=x.findall('.//y:Label.Text',ns)
 label=''.join(t.text or '' for t in texts)
 m=re.search(r'(?m)^(\d{3}) · ([A-Z]+\d+[A-Z]?)$',label)
 if not m:
  errors.append(f'GraphML unresolved label {x.attrib.get("id")}')
 else:
  semantic_labels[m.group(2)]=m.group(1)
if set(semantic_labels)!=idset:errors.append('GraphML semantic node IDs')
for n in N:
 if semantic_labels.get(n['id'])!=n['node_number']:errors.append(f'label {n["id"]}')
# Python/Lean code paths and imports are prefix-free.
for path in (ROOT/'derivation/code/python').rglob('*.py'):
 if 'soll_' in path.name: errors.append(f'Python legacy basename {path.relative_to(ROOT)}')
 text=path.read_text(encoding='utf-8')
 if re.search(r'(^|\.)soll_[a-z0-9_]+', text): errors.append(f'Python legacy import token {path.relative_to(ROOT)}')
for path in (ROOT/'derivation/code/lean').rglob('*.lean'):
 if 'SOLL_' in path.name: errors.append(f'Lean legacy basename {path.relative_to(ROOT)}')
 text=path.read_text(encoding='utf-8')
 if re.search(r'^\s*import\s+.*SOLL_', text, re.M): errors.append(f'Lean legacy import token {path.relative_to(ROOT)}')
result={'schema':'cnna.g0-canonical-dag-audit.v1','status':'PASS' if not errors else 'FAIL','nodes':len(N),'edges':len(E),'hard_edges':sum(e['hard_dependency']=='true' for e in E),'proof_certification_edges':sum(e['edge_class']=='PROOF_CERTIFICATION' for e in E),'graph_roots':sorted(actual_roots,key=lambda i:int(nd[i]['derivation_order'])),'top_visible_roots':['I001','I002','C001'],'weak_components':1 if len(reach)==145 else None,'canonical_id_format':'PREFIX_FREE','node_label_format':'NNN · ID','errors':errors}
(DAG/'G0_AUDIT.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(result,ensure_ascii=False,indent=2))
sys.exit(1 if errors else 0)
