#!/usr/bin/env python3
from pathlib import Path
import csv,json,sys
ROOT=Path(__file__).resolve().parents[3]
errors=[]
def rows(p):
 with p.open(encoding="utf-8",newline="") as f:return list(csv.DictReader(f,delimiter="\t"))
identity=json.loads((ROOT/"PROJECT_IDENTITY.json").read_text())
if identity.get("framework")!="Generalized Open Provenance Systems":errors.append("project identity")
ns=rows(ROOT/"derivation/registry/dag/NODES.tsv"); ids={r["id"] for r in ns}
m=rows(ROOT/"derivation/registry/OPEN_PROVENANCE_NODE_MAP.tsv")
if not m or any(r["node_id"] not in ids for r in m):errors.append("node map")
required={"C003","C018","C005","C004","M001","C006","C007","M003","P001","M004","C008","C016","C017","C024","C043","C044","C045","C047","C046","C053","C060","M080"}
for nid in required:
 d=json.loads((ROOT/f"derivation/registry/nodes/{nid}.json").read_text())
 if not d.get("open_provenance_context"):errors.append("missing context "+nid)
for nid in {"C003","C018","C005","C004","M001","C006","C007","M003","P001","M004"}:
 d=json.loads((ROOT/f"derivation/registry/nodes/{nid}.json").read_text())
 for key in ("main_artifact","supplement_artifact"):
  t=(ROOT/d["section_hierarchy"][key]).read_text()
  if f"CNNA-OPEN-PROVENANCE-BEGIN {nid}" not in t:errors.append("missing prose marker "+nid+" "+key)
fw=(ROOT/"derivation/registry/documentation/OPEN_PROVENANCE_FRAMEWORK.md").read_text()
for phrase in ["not currently proved","not a partial trace","Legacy migration target","did **not** establish"]:
 if phrase not in fw:errors.append("missing guard "+phrase)
if errors:
 print("\n".join("FAIL "+e for e in errors));sys.exit(1)
print(f"OPEN_PROVENANCE_INTEGRATION PASS entries={len(m)} nodes={len({r['node_id'] for r in m})}")
