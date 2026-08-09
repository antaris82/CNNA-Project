#!/usr/bin/env python3
"""Guard the editor-owned canonical yEd Live layout.

The canonical GraphML geometry is supplied and maintained in yEd Live. This
project tool deliberately does not regenerate or relayout it. Run validate_g2.py
to check semantic coverage and centred labels. A complete relayout requires an
explicit editor decision and must not be performed by an automated package gate.
"""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[3]
GRAPH = ROOT / 'derivation/registry/dag/DAG_yEd.graphml'
if not GRAPH.is_file():
    print('ERROR canonical yEd GraphML is missing', file=sys.stderr)
    raise SystemExit(1)
print('CANONICAL_YED_LAYOUT_PRESERVED')
print(GRAPH.relative_to(ROOT))
