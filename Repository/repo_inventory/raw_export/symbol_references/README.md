# Symbol reference export

This directory exports a heuristic symbol-level refinement of the import graph.

- Modules scanned: **287**
- Declarations detected: **8860**
- Modules with open namespaces: **220**
- Opened namespaces detected: **815**
- Symbol-reference edges: **394**
- Referenced symbols: **1686**
- Confidence counts: `{'anchored_open_namespace': 78, 'exact_qualified': 79, 'imported_unique_alias': 62, 'qualified_suffix': 5247, 'same_namespace_short_name': 192}`

## Files

- `declarations.json`: detected declaration names and open namespaces per module
- `references.json`: detected cross-module symbol references aggregated by consumer/dependency
- `semantic_signal_plan/summary.json`: refined signal-plan export using only detected symbol-reference edges

## Scope note

The analysis remains conservative. It detects declarations, open namespaces and alias-like references syntactically; it does not run Lean elaboration and therefore cannot prove that every hit is semantically resolved exactly as detected.
