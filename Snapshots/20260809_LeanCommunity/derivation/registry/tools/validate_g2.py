#!/usr/bin/env python3
from pathlib import Path
import csv, json, re, sys
from lxml import etree

ROOT = Path(__file__).resolve().parents[3]
DAG = ROOT / 'derivation/registry/dag'

def rows(path):
    with path.open(encoding='utf-8', newline='') as handle:
        return list(csv.DictReader(handle, delimiter='\t'))

nodes = rows(DAG / 'NODES.tsv')
edges = rows(DAG / 'EDGES.tsv')
by = {n['id']: n for n in nodes}
errors = []
tree = etree.parse(str(DAG / 'DAG_yEd.graphml'))
ns = {
    'g': 'http://graphml.graphdrawing.org/xmlns',
    'y': 'http://www.yworks.com/xml/yfiles-common/3.0',
}
graph_nodes = tree.xpath('//g:node', namespaces=ns)
graph_edges = tree.xpath('//g:edge', namespaces=ns)
if len(graph_nodes) != 145:
    errors.append(f'nodes={len(graph_nodes)}')
if len(graph_edges) != 401:
    errors.append(f'edges={len(graph_edges)}')

xml_to_id = {}
positions = {}
centered = []
for node in graph_nodes:
    label = ''.join(node.xpath('.//y:Label.Text/text()', namespaces=ns))
    match = re.search(r'(?m)^(\d{3}) · ([A-Z]+\d+[A-Z]?)$', label)
    if not match:
        errors.append('unresolved node label ' + node.get('id'))
        continue
    number, node_id = match.groups()
    xml_to_id[node.get('id')] = node_id
    if node_id not in by or by[node_id]['node_number'] != number:
        errors.append('node label mismatch ' + node_id)
    rect = node.xpath('.//y:RectD', namespaces=ns)
    if rect:
        positions[node_id] = (float(rect[0].get('X')), float(rect[0].get('Y')))
    labels = node.xpath('.//y:Label', namespaces=ns)
    styles = node.xpath('.//y:Label.Style/*', namespaces=ns)
    is_centered = bool(
        labels
        and labels[0].get('LayoutParameter') == '{x:Static yx:StretchNodeLabelModel.Center}'
        and styles
        and styles[0].get('verticalTextAlignment') == 'CENTER'
        and styles[0].get('horizontalTextAlignment') == 'CENTER'
    )
    if is_centered:
        centered.append(node_id)

if set(xml_to_id.values()) != set(by):
    errors.append('GraphML semantic ID mismatch')
if len(centered) != 145:
    errors.append(f'centered={len(centered)}')

pairs = []
for edge in graph_edges:
    source = xml_to_id.get(edge.get('source'))
    target = xml_to_id.get(edge.get('target'))
    labels = edge.xpath('.//y:Label/@Text', namespaces=ns)
    pairs.append((source, target, labels[0] if labels else ''))
expected_pairs = {(e['source'], e['target']) for e in edges}
if {(s, t) for s, t, _ in pairs} != expected_pairs:
    errors.append('GraphML edge endpoint semantics mismatch')
relation_by_pair = {(e['source'], e['target']): e['relation'] for e in edges}
for source, target, label in pairs:
    if label and relation_by_pair.get((source, target)) != label:
        errors.append('visible edge label mismatch ' + str((source, target, label)))

origin_positions = {node_id: positions.get(node_id) for node_id in ['I001', 'I002', 'C001']}
if any(value is None for value in origin_positions.values()):
    errors.append('origin-node geometry missing')

result = {
    'schema': 'cnna.g2-user-yed-live-canonical-layout-audit.v1',
    'status': 'PASS' if not errors else 'FAIL',
    'layout_authority': 'USER_SUPPLIED_YED_LIVE_GRAPHML',
    'nodes': len(graph_nodes),
    'edges': len(graph_edges),
    'centered_labels': len(centered),
    'origin_nodes': ['I001', 'I002', 'C001'],
    'origin_positions': origin_positions,
    'geometry_preservation_policy': 'DO_NOT_RELAYOUT_WITH_PROJECT_RENDERER',
    'errors': errors,
}
(DAG / 'G2_AUDIT.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print(json.dumps(result, indent=2))
sys.exit(1 if errors else 0)
