#!/usr/bin/env python3
import csv
import json
import re
import subprocess
from pathlib import Path
from collections import Counter
from typing import Dict, List, Set, Any, Tuple
import yaml

ROOT = Path(__file__).resolve().parents[1]
M = ROOT / 'masters'
T = ROOT / 'tables'
E = ROOT / 'generated_exports'
T.mkdir(exist_ok=True)
E.mkdir(exist_ok=True)

MASTER_FILE = M / 'cnna_roadmap_master.yaml'
PHASE_STATUS = {'G', 'O', 'Y', 'R', 'W'}
COMPLETED_IMPL = {'completed'}
ALLOWED_OBJECT_STATUS = {'W', 'B', 'G', 'Y', 'R', 'K'}


def fail(msg: str) -> None:
    raise SystemExit(f'generate_tables.py validation error: {msg}')


def load_master() -> Dict[str, Any]:
    # Hard single-source rule: no legacy master TSV/YAML files may be present.
    if not MASTER_FILE.exists():
        fail('masters/cnna_roadmap_master.yaml is missing')
    stale = [p.name for p in M.glob('*.tsv')] + [p.name for p in M.glob('implementation_scratchpad.yaml')]
    if stale:
        fail('stale legacy master files found in masters/: ' + ', '.join(sorted(stale)) + '; edit only cnna_roadmap_master.yaml')
    data = yaml.safe_load(MASTER_FILE.read_text(encoding='utf-8'))
    if not isinstance(data, dict):
        fail('cnna_roadmap_master.yaml must contain a mapping')
    required = ['metadata', 'latest_change_overview', 'status_legend', 'access_policy', 'code_audit', 'format_decision', 'workflow_policy', 'pre_implementation_phase_check_policy', 'pre_implementation_phase_check_results', 'implementation_scaling_phase_plan', 'global_no_go_guardrails', 'global_postulates', 'phase_object_link_policy', 'phases', 'objects', 'implementation_scratchpad', 'object_proof_dossiers', 'reuse_duplication_ledger', 'consumption_classification_map', 'context_class_taxonomy', 'object_significance_taxonomy', 'lean_declaration_classification_taxonomy']
    for key in required:
        if key not in data:
            fail(f'master file is missing top-level section {key}')
    return data


def esc(s: str) -> str:
    if s is None:
        return ''
    out = []
    for ch in str(s):
        if ch == '&': out.append(r'\&')
        elif ch == '%': out.append(r'\%')
        elif ch == '$': out.append(r'\$')
        elif ch == '#': out.append(r'\#')
        elif ch == '_': out.append(r'\_')
        elif ch == '{': out.append(r'\{')
        elif ch == '}': out.append(r'\}')
        elif ch == '~': out.append(r'\textasciitilde{}')
        elif ch == '^': out.append(r'\textasciicircum{}')
        elif ch == '\\': out.append(r'\textbackslash{}')
        elif ch == '/': out.append(r'/\allowbreak{}')
        else: out.append(ch)
    s = ''.join(out)
    s = s.replace('; ', r';\newline ')
    return s


def list_tex(items) -> str:
    if not items:
        return '---'
    if isinstance(items, str):
        items = [items]
    return r'\begin{itemize}[leftmargin=*,itemsep=0.05em,topsep=0.05em]' + ''.join(rf'\item {esc(x)}' for x in items) + r'\end{itemize}'


def normalize_rows(section: Any, section_name: str) -> List[Dict[str, str]]:
    if not isinstance(section, list):
        fail(f'{section_name} must be a list of records')
    rows: List[Dict[str, str]] = []
    for idx, item in enumerate(section):
        if not isinstance(item, dict):
            fail(f'{section_name}[{idx}] is not a record')
        rows.append({str(k): '' if v is None else str(v) for k, v in item.items()})
    return rows


def write_export_tsv(name: str, rows: List[Dict[str, str]]) -> None:
    if not rows:
        return
    path = E / name
    headers = list(rows[0].keys())
    with path.open('w', encoding='utf-8', newline='') as f:
        w = csv.DictWriter(f, delimiter='\t', fieldnames=headers)
        w.writeheader()
        w.writerows(rows)


def status_cell(code: str) -> str:
    colors = {'W': 'white', 'B': 'cyan!20', 'G': 'green!18', 'O': 'orange!28', 'Y': 'yellow!25', 'R': 'red!20', 'K': 'black!18'}
    return rf'\cellcolor{{{colors.get(code, "white")}}}{esc(code)}'


def phase_label(phase: str) -> str:
    return 'impl:phase-' + str(phase).replace('.', '-')


def phase_row_anchor(phase: str) -> str:
    return 'phase-row-' + str(phase).replace('.', '-')


def object_row_anchor(obj_id: str) -> str:
    return 'object-row-' + str(obj_id).replace('.', '-')


def phase_table_phase_cell(phase: str) -> str:
    return rf'\hypertarget{{{phase_row_anchor(phase)}}}{{{esc(phase)}}}'


def object_table_id_cell(obj_id: str, target: bool = False) -> str:
    oid = esc(obj_id)
    if target:
        proof_anchor = 'objproof:' + str(obj_id).replace('.', '-')
        return rf'\hypertarget{{{object_row_anchor(obj_id)}}}{{\hyperlink{{{proof_anchor}}}{{{oid}}}}}'
    return rf'\hyperlink{{{object_row_anchor(obj_id)}}}{{{oid}}}'


def phase_link_cell(phase: str) -> str:
    return rf'\hyperlink{{{phase_row_anchor(phase)}}}{{{esc(phase)}}}' if phase else '---'


def object_link_cell(obj_ids) -> str:
    if not obj_ids:
        return '---'
    return ', '.join(rf'\hyperlink{{{object_row_anchor(oid)}}}{{{esc(oid)}}}' for oid in obj_ids)

def context_class_cell(value: str) -> str:
    text = str(value or '')
    if len(text) <= 14:
        return esc(text)
    parts = re.findall(r'[A-Z]+(?=[A-Z][a-z]|$)|[A-Z]?[a-z]+|[0-9]+', text)
    if not parts:
        return esc(text)
    return esc('; '.join(parts))

def object_link_policy_cell(phase: str, obj_ids, policy: str, reason: str, child_scope: str) -> str:
    policy = (policy or '').strip()
    reason = (reason or '').strip()
    child_scope = (child_scope or '').strip()
    if policy == 'direct':
        if not obj_ids:
            fail(f'phase {phase} declares direct object-link policy but has no direct objects')
        return object_link_cell(obj_ids)
    if policy == 'scope_only':
        if obj_ids:
            fail(f'phase {phase} declares scope_only but also has direct objects')
        if not child_scope:
            fail(f'phase {phase} declares scope_only but has no child-object scope summary')
        return r'\textit{scope-only}; child objects: ' + esc(child_scope)
    if policy == 'no_direct_object':
        if obj_ids:
            fail(f'phase {phase} declares no_direct_object but has direct objects')
        return r'\textit{no direct object}: ' + esc(reason or 'audit/baseline/closeout phase')
    if policy == 'moved':
        if obj_ids:
            # moved phases should not normally own objects; render explicitly if they do for audit visibility.
            return object_link_cell(obj_ids) + r'; \textit{moved/audit note}: ' + esc(reason or 'ownership moved elsewhere')
        return r'\textit{moved}: ' + esc(reason or 'ownership moved elsewhere')
    fail(f'phase {phase} has invalid Object link policy {policy}')


def phase_record_link(phase: str, status: str, scratch_by_phase: Dict[str, Dict]) -> str:
    if phase in scratch_by_phase:
        if status == 'G': text = 'implemented record'
        elif status == 'Y': text = 'active scratch pad'
        elif status == 'R': text = 'blocked scratch pad'
        else: text = 'planned scratch pad'
        return rf'\hyperref[{phase_label(phase)}]{{{esc(text)}}}'
    if status == 'G':
        fail(f'green phase {phase} has no implementation scratch-pad record')
    return 'pending'


def validate_phase_hierarchy(phase_ids: List[str]) -> None:
    seen: Set[str] = set()
    for ph in phase_ids:
        if ph in seen:
            fail(f'duplicate phase_id {ph}')
        seen.add(ph)
    for ph in phase_ids:
        parts = ph.split('.')
        for i in range(1, len(parts)):
            parent = '.'.join(parts[:i])
            if parent not in seen:
                fail(f'phase {ph} exists but parent phase {parent} is missing')


def validate_inputs(phase_rows: List[Dict[str, str]], scratch_rows: List[Dict[str, str]]) -> Dict[str, Dict[str, str]]:
    if not phase_rows:
        fail('master phases section is empty')
    phase_ids = [r['Phase'] for r in phase_rows]
    validate_phase_hierarchy(phase_ids)
    phase_status = {r['Phase']: r['Phase status'] for r in phase_rows}
    for ph, st in phase_status.items():
        if st not in PHASE_STATUS:
            fail(f'phase {ph} has invalid phase status {st}')
    active = [ph for ph, st in phase_status.items() if st == 'Y']
    if len(active) != 1:
        fail(f'exactly one active phase with status Y is required; found {active}')
    for forbidden in ('How implemented', 'Linked objects'):
        if forbidden in phase_rows[0]:
            fail(f'master phases section must not contain generated column {forbidden}')
    required_phase_fields = {'Object link policy', 'Object link explanation', 'Child object scope', 'Context class', 'Phase documentation tier', 'Phase documentation depth requirement'}
    missing_phase_fields = required_phase_fields.difference(phase_rows[0].keys())
    if missing_phase_fields:
        fail('master phases section misses required object-link policy fields: ' + ', '.join(sorted(missing_phase_fields)))
    allowed_object_link_policies = {'direct', 'scope_only', 'no_direct_object', 'moved'}
    for r in phase_rows:
        pol = str(r.get('Object link policy', '')).strip()
        if pol not in allowed_object_link_policies:
            fail(f'phase {r.get("Phase", "?")} has invalid Object link policy {pol}')
        if pol != 'direct' and not str(r.get('Object link explanation', '')).strip():
            fail(f'phase {r.get("Phase", "?")} has non-direct Object link policy without explanation')
        if not str(r.get('Context class', '')).strip():
            fail(f'phase {r.get("Phase", "?")} has empty Context class')
        if str(r.get('Phase documentation tier', '')).strip() not in {'F0', 'F1', 'F2', 'F3', 'F4'}:
            fail(f'phase {r.get("Phase", "?")} has invalid Phase documentation tier {r.get("Phase documentation tier", "")}')
        if not str(r.get('Phase documentation depth requirement', '')).strip():
            fail(f'phase {r.get("Phase", "?")} has empty Phase documentation depth requirement')

    required_scratch_fields = {
        'phase_id', 'phase_status', 'implementation_status', 'title', 'how_implemented',
        'verification_evidence', 'implementation_notes', 'implemented_modules', 'added_modules',
        'modified_modules', 'proof_strategy', 'build_result', 'forbidden_patterns_checked',
        'preparation_status', 'preparation_workflow', 'source_materials',
        'extracted_theory_objects', 'source_to_cnna_mapping', 'dependency_depth_audit',
        'phase_split_decision', 'positive_path_plan', 'proof_rehearsal', 'expected_tactics',
        'expected_mathlib_imports', 'exec_complex_plan', 'bridge_gap_status',
        'natural_backjump_or_refactor_layer', 'implementation_prompt_contract',
        'no_go_guardrails', 'post_implementation_plan_check', 'artifact_packaging_rule', 'global_no_go_inheritance',
        'concrete_instance_traversal', 'computable_path_not_skeleton_status',
        'expected_executable_witness', 'mathlib_complication_log',
        'noncomputable_boundary_audit', 'mathlib_mitigation_or_refactor_layer',
        'phase_type', 'phase_type_specific_contract', 'refactor_regression_protocol',
        'refactor_migration_metrics', 'lean_mathlib_version_policy',
        'exec_complex_boundary_policy', 'consumer_contract_direction',
        'governance_overhead_review',
        'module_implementation_manifest', 'semantic_placement_decision',
        'reuse_and_duplication_audit', 'canonical_generator_policy',
        'module_compactness_rule', 'proposed_added_modules',
        'proposed_modified_modules', 'reusable_existing_modules',
        'duplicate_risk_symbols'
    }
    scratch_by_phase: Dict[str, Dict[str, str]] = {}
    for rec in scratch_rows:
        missing_scratch = required_scratch_fields.difference(rec.keys())
        if missing_scratch:
            fail('scratch-pad record misses required fields: ' + ', '.join(sorted(missing_scratch)))
        ph = str(rec.get('phase_id', '')).strip()
        if not ph:
            fail('scratch-pad record without phase_id')
        if ph in scratch_by_phase:
            fail(f'duplicate scratch-pad record for phase {ph}')
        if ph not in phase_status:
            fail(f'scratch-pad record references unknown phase {ph}')
        scratch_by_phase[ph] = rec
        sp_st = str(rec.get('phase_status', '')).strip()
        if sp_st != phase_status[ph]:
            fail(f'scratch-pad phase_status for {ph} is {sp_st}, but phase table says {phase_status[ph]}')
        impl = str(rec.get('implementation_status', '')).strip()
        pt = str(rec.get('phase_type', '')).strip()
        allowed_phase_types = {'baseline', 'infrastructure', 'refactor', 'derivation', 'comparison', 'documentation'}
        if pt not in allowed_phase_types:
            fail(f'scratch-pad phase {ph} has invalid phase_type {pt}')
        if pt == 'derivation' and phase_status[ph] == 'W':
            fail(f'derivation phase {ph} may not be white under V1.19 status policy; use R until released by derived-only object evidence, Y when active, O when implementable after predecessor closure, or G when closed')
        if phase_status[ph] == 'G' and impl not in COMPLETED_IMPL:
            fail(f'green phase {ph} must have implementation_status completed; found {impl}')
        if phase_status[ph] == 'W' and impl in COMPLETED_IMPL:
            fail(f'white phase {ph} may not have completed implementation_status')
        if phase_status[ph] == 'Y' and impl in COMPLETED_IMPL:
            fail(f'active phase {ph} may not already be completed')
        if phase_status[ph] == 'Y':
            for required_active in ('dependency_depth_audit', 'proof_rehearsal', 'positive_path_plan', 'no_go_guardrails', 'concrete_instance_traversal', 'mathlib_complication_log', 'noncomputable_boundary_audit', 'module_implementation_manifest', 'semantic_placement_decision'):
                val = rec.get(required_active, '')
                if val in ('', [], None) or str(val).strip().lower() in {'not prepared yet.', 'pending.'}:
                    fail(f'active phase {ph} lacks prepared scratch-pad field {required_active}')
    for ph in phase_status:
        if ph not in scratch_by_phase:
            fail(f'phase {ph} has no scratch-pad record; every phase row must link to the generated implementation scratch pad')
    return scratch_by_phase


def validate_object_register(obj_rows: List[Dict[str, str]], phase_rows: List[Dict[str, str]]) -> None:
    if not obj_rows:
        fail('master objects section is empty')
    ids: Set[str] = set()
    phase_ids = {r['Phase'] for r in phase_rows}
    required_cols = {
        'ID', 'Object', 'Layer', 'Canonical CNNA definition', 'Natural provenance',
        'Computed from', 'ExecComplex/computable path', 'Object status', 'Code status',
        'Current code modules / derivation site', 'Neutral target location / canonical API',
        'Pillar-A access', 'Handoff rights', 'May be consumed by', 'Priority', 'Phase',
        'Proof documentation status', 'Proof dossier', 'Context class', 'Significance tier', 'Documentation depth requirement',
        'Object lifecycle state', 'Lifecycle predecessor object(s)', 'Lifecycle successor/current object', 'Lifecycle note', 'Current dossier pointer'
    }
    missing = required_cols.difference(obj_rows[0].keys())
    if missing:
        fail('master objects section misses required columns: ' + ', '.join(sorted(missing)))
    for r in obj_rows:
        oid = r['ID'].strip()
        if not oid:
            fail('master objects section contains a row without ID')
        if oid in ids:
            fail(f'duplicate object ID {oid}')
        ids.add(oid)
        st = r['Object status'].strip()
        if st not in ALLOWED_OBJECT_STATUS:
            fail(f'object {oid} has invalid Object status {st}')
        phase = r['Phase'].strip()
        if st != 'W' and not phase:
            fail(f'non-white object {oid} must reference a phase')
        if phase and phase not in phase_ids:
            fail(f'object {oid} references unknown phase {phase}')
        proof_status = r.get('Proof documentation status', '').strip()
        if not proof_status:
            fail(f'object {oid} has empty Proof documentation status')
        if not r.get('Context class', '').strip():
            fail(f'object {oid} has empty Context class')
        if r.get('Significance tier', '').strip() not in {'F0', 'F1', 'F2', 'F3', 'F4'}:
            fail(f'object {oid} has invalid Significance tier {r.get("Significance tier", "")}')
        if not r.get('Documentation depth requirement', '').strip():
            fail(f'object {oid} has empty Documentation depth requirement')
        lifecycle_state = r.get('Object lifecycle state', '').strip()
        allowed_lifecycle_states = {'current', 'superseded', 'renamed-alias', 'deleted-retired', 'historical'}
        if lifecycle_state not in allowed_lifecycle_states:
            fail(f'object {oid} has invalid Object lifecycle state {lifecycle_state}; expected one of {sorted(allowed_lifecycle_states)}')
        if not r.get('Lifecycle note', '').strip():
            fail(f'object {oid} has empty Lifecycle note')
        if not r.get('Current dossier pointer', '').strip():
            fail(f'object {oid} has empty Current dossier pointer')
        proof_dossier = r.get('Proof dossier', '').strip()
        expected_proof_dossier = f'proof:{oid}'
        if proof_dossier != expected_proof_dossier:
            fail(f'object {oid} Proof dossier must be {expected_proof_dossier}; found {proof_dossier}')
        current_dossier = r.get('Current dossier pointer', '').strip()
        if not current_dossier.startswith('proof:'):
            fail(f'object {oid} Current dossier pointer must start with proof:; found {current_dossier}')
    for r in obj_rows:
        oid = r['ID'].strip()
        successor = r.get('Lifecycle successor/current object', '').strip()
        if successor and successor != 'none' and successor not in ids:
            fail(f'object {oid} has dangling Lifecycle successor/current object {successor}')


def phase_object_map(obj_rows: List[Dict[str, str]], phase_rows: List[Dict[str, str]]) -> Dict[str, List[str]]:
    mapping: Dict[str, List[str]] = {r['Phase']: [] for r in phase_rows}
    for r in obj_rows:
        ph = r.get('Phase', '').strip()
        if ph:
            mapping.setdefault(ph, []).append(r['ID'].strip())
    return mapping


def table_legend_tex(kind: str) -> str:
    legends = {
        'static': (
            r'\par\smallskip\noindent\begin{minipage}{0.99\linewidth}\footnotesize\raggedright\textbf{Table legend.} '
            r'\colorbox{red!20}{\strut R} = red/urgent; '
            r'\colorbox{yellow!25}{\strut Y} = yellow/critical; '
            r'\colorbox{green!18}{\strut G} = green/closed.'
            r'\end{minipage}\par\vspace{0.25em}'
        ),
        'phase': (
            r'\par\smallskip\noindent\begin{minipage}{0.99\linewidth}\footnotesize\raggedright\textbf{Table legend.} '
            r'\colorbox{green!18}{\strut G} = green/closed and derived-only; '
            r'\colorbox{white}{\strut W} = white/non-direct-Lean tooling/refactor/infrastructure/documentation/comparison; '
            r'\colorbox{orange!28}{\strut O} = orange/implementable after stated predecessor closure; '
            r'\colorbox{yellow!25}{\strut Y} = yellow/active and implementable now; '
            r'\colorbox{red!20}{\strut R} = red/locked Lean-derivation phase; release requires derived-only object/proof evidence. Context class is orthogonal to status.'
            r'\end{minipage}\par\vspace{0.25em}'
        ),
        'object': (
            r'\par\smallskip\noindent\begin{minipage}{0.99\linewidth}\footnotesize\raggedright\textbf{Table legend.} '
            r'\colorbox{white}{\strut W} = white/finished public object; '
            r'\colorbox{cyan!20}{\strut B} = blue/proof-carrying but semantic/API correction still open; '
            r'\colorbox{green!18}{\strut G} = green/locally closable; '
            r'\colorbox{yellow!25}{\strut Y} = yellow/known route with prerequisites; '
            r'\colorbox{red!20}{\strut R} = red/derivation layer incomplete or unclear; '
            r'\colorbox{black!18}{\strut K} = black/registered side or future target. Context class is orthogonal to status.'
            r'\end{minipage}\par\vspace{0.25em}'
        ),
        'precheck': (
            r'\par\smallskip\noindent\begin{minipage}{0.99\linewidth}\footnotesize\raggedright\textbf{Table legend.} '
            r'\colorbox{green!18}{\strut G} = green/closed and derived-only; '
            r'\colorbox{orange!28}{\strut O} = orange/implementable after stated predecessor closure; '
            r'\colorbox{yellow!25}{\strut Y} = yellow/active and implementable now; '
            r'\colorbox{red!20}{\strut R} = red/locked Lean-derivation phase; release requires derived-only object/proof evidence. Context class is orthogonal to status.'
            r'\end{minipage}\par\vspace{0.25em}'
        ),
    }
    if kind not in legends:
        fail(f'unknown table legend kind {kind}')
    return legends[kind]


def write_table_legend(f, kind: str) -> None:
    f.write(table_legend_tex(kind) + '\n')


def longtable(headers, widths, data, path, size=r'\small', status_cols=None, raw_cols=None, legend: str = None):
    status_cols = status_cols or set()
    raw_cols = raw_cols or set()
    if abs(sum(widths) - sum(widths)) > 1:  # no-op, keeps lint quiet
        pass
    with (T / path).open('w', encoding='utf-8') as f:
        f.write(size + '\n')
        if legend:
            write_table_legend(f, legend)
        f.write(r'\arrayrulecolor{black!22}' + '\n')
        f.write('\\begin{longtable}{' + ' '.join(f'L{{{w}\\linewidth}}' for w in widths) + '}\n')
        f.write('\\hline\n')
        f.write(' & '.join(rf'\textbf{{{esc(h)}}}' for h in headers) + '\\\\\n')
        f.write('\\hline\n\\endfirsthead\n')
        f.write('\\hline\n')
        f.write(' & '.join(rf'\textbf{{{esc(h)}}}' for h in headers) + '\\\\\n')
        f.write('\\hline\n\\endhead\n')
        for row in data:
            cells = []
            for h in headers:
                v = row.get(h, '')
                if h in raw_cols:
                    cells.append(v)
                elif h in status_cols:
                    cells.append(status_cell(v))
                else:
                    cells.append(esc(v))
            f.write(' & '.join(cells) + '\\\\\n')
            f.write('\\hline\n')
            f.write('\\addlinespace[0.24em]\n')
        f.write('\\end{longtable}\n')
        f.write(r'\arrayrulecolor{black}' + '\n')
        f.write('\\normalsize\n')


def static_finding_priority_cell(priority: str) -> str:
    colors = {'R': 'red!20', 'Y': 'yellow!25', 'G': 'green!18'}
    return rf'\cellcolor{{{colors.get(priority, "white")}}}{esc(priority)}'

def write_code_audit(rows: List[Dict[str, str]]) -> None:
    if not rows:
        fail('code_audit section is empty')
    required = {'ID', 'Priority', 'Issue status', 'Addressing phase', 'Change version', 'Change timestamp', 'Finding', 'Static observation', 'Risk', 'Refactoring consequence'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('code_audit misses required columns: ' + ', '.join(sorted(missing)))
    ids = [str(r.get('ID', '')).strip() for r in rows]
    if len(ids) != len(set(ids)):
        fail('code_audit contains duplicate IDs')
    allowed_priorities = {'R', 'Y', 'G'}
    for r in rows:
        rid = str(r.get('ID', '')).strip()
        if not rid:
            fail('code_audit contains a row without ID')
        pri = str(r.get('Priority', '')).strip()
        if pri not in allowed_priorities:
            fail(f'code_audit row {rid} has invalid Priority {pri}; expected R, Y, or G')
        issue_status = str(r.get('Issue status', '')).strip().lower()
        if pri == 'G' and not issue_status.startswith('closed'):
            fail(f'code_audit row {rid} uses green triage but Issue status is not closed')
        if issue_status.startswith('closed') and pri != 'G':
            fail(f'code_audit row {rid} is closed but not marked with green triage')
        for key in ('Issue status', 'Addressing phase', 'Change version', 'Change timestamp', 'Finding', 'Static observation', 'Risk', 'Refactoring consequence'):
            if not str(r.get(key, '')).strip():
                fail(f'code_audit row {rid} has empty {key}')
    longtable(
        ['ID', 'Priority', 'Issue status', 'Addressing phase', 'Change version', 'Change timestamp', 'Finding', 'Static observation', 'Risk', 'Refactoring consequence'],
        [0.030, 0.026, 0.087, 0.085, 0.052, 0.085, 0.095, 0.205, 0.130, 0.165],
        rows,
        'code_audit_table.tex',
        r'\footnotesize',
        {'Priority'},
        legend='static'
    )
    text = r"""\paragraph{Static finding triage rule.} This table is sourced from the Master YAML code-audit ledger. Every static finding is a tracked issue, not loose prose. Each row records the tool/change version and timestamp at which the issue record was last materially changed. Static-finding colors are: \textbf{R/red = urgent}, \textbf{Y/yellow = critical}, \textbf{G/green = closed}. New static problems discovered during feasibility checks, implementation, or review must be added here with an ID, lifecycle status, and addressing phase before work continues.
\input{tables/code_audit_table.tex}
"""
    (T / 'code_audit.tex').write_text(text, encoding='utf-8')

def version_meta(metadata: Dict[str, Any], key: str, fallback: str = '') -> str:
    aliases = {
        'tool_infrastructure_version': ('tool_infrastructure_version', 'tool_version'),
        'tool_infrastructure_timestamp': ('tool_infrastructure_timestamp', 'tool_change_timestamp'),
        'planning_data_version': ('planning_data_version',),
        'planning_data_timestamp': ('planning_data_timestamp',),
        'lean_data_version': ('lean_data_version', 'data_version'),
        'lean_data_timestamp': ('lean_data_timestamp', 'data_timestamp'),
    }
    for candidate in aliases.get(key, (key,)):
        value = metadata.get(candidate)
        if value not in (None, ''):
            return str(value)
    return fallback


def write_latest_change_overview(metadata: Dict[str, Any], rows: List[Dict[str, str]]) -> None:
    if not isinstance(metadata, dict):
        fail('metadata must be a record')
    required_meta = {'tool_infrastructure_version', 'tool_infrastructure_timestamp', 'planning_data_version', 'planning_data_timestamp', 'lean_data_version', 'lean_data_timestamp'}
    missing_meta = {k for k in required_meta if not version_meta(metadata, k)}
    if missing_meta:
        fail('metadata misses required three-layer version fields: ' + ', '.join(sorted(missing_meta)))
    if not rows:
        fail('latest_change_overview section is empty')
    required = {'Item', 'State'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('latest_change_overview misses required columns: ' + ', '.join(sorted(missing)))
    overview_rows = [
        {'Item': 'Tool infrastructure version', 'State': version_meta(metadata, 'tool_infrastructure_version')},
        {'Item': 'Tool infrastructure timestamp', 'State': version_meta(metadata, 'tool_infrastructure_timestamp')},
        {'Item': 'Planning data version', 'State': version_meta(metadata, 'planning_data_version')},
        {'Item': 'Planning data timestamp', 'State': version_meta(metadata, 'planning_data_timestamp')},
        {'Item': 'Lean toolchain version', 'State': version_meta(metadata, 'lean_data_version')},
        {'Item': 'Lean data timestamp', 'State': version_meta(metadata, 'lean_data_timestamp')},
        {'Item': 'Document title', 'State': str(metadata.get('document', ''))},
    ] + rows
    write_export_tsv('latest_change_overview.generated.tsv', overview_rows)
    longtable(['Item', 'State'], [0.18, 0.78], overview_rows, 'latest_change_overview_table.tex', r'\small')
    (T / 'latest_change_overview.tex').write_text(r'''\paragraph{Latest change overview.} This section records the current timestamp-complete three-layer version state. \textbf{Lean toolchain version + Lean data timestamp} is intentionally asymmetric: the version records the Lean toolchain/API level, while the timestamp advances only when Lean source/data changes. \textbf{Planning data version+timestamp} advances when the YAML planning registers, phase list, object list, scratchpads, proof dossiers, policy ledgers, or generated planning data change. \textbf{Tool infrastructure version+timestamp} advances only when generator/frontend/importer/tool code changes. A version without its paired timestamp is invalid for history, SQL mirrors, Explorer provenance and generated release metadata. Legacy metadata aliases remain only for backward compatibility and may not be used to infer a Lean data change or collapse toolchain version with source snapshot time.
\input{tables/latest_change_overview_table.tex}
''', encoding='utf-8')


def write_status_explanation_tables(status_rows: List[Dict[str, str]]) -> None:
    if not isinstance(status_rows, list):
        fail('status_legend must be a list of records')
    rows = [{str(k): '' if v is None else str(v) for k, v in r.items()} for r in status_rows]
    object_rows = [{'Code': r.get('Code', ''), 'Meaning': r.get('Meaning', '')} for r in rows if r.get('System') == 'Object status']
    phase_rows = [{'Code': r.get('Code', ''), 'Meaning': r.get('Meaning', '')} for r in rows if r.get('System') == 'Phase status']
    if not object_rows:
        fail('status_legend contains no Object status rows')
    if not phase_rows:
        fail('status_legend contains no Phase status rows')
    longtable(['Code', 'Meaning'], [0.045, 0.925], object_rows, 'object_status_explanation.tex', r'\small', {'Code'}, legend='object')
    longtable(['Code', 'Meaning'], [0.045, 0.925], phase_rows, 'phase_status_explanation.tex', r'\small', {'Code'}, legend='phase')


def write_workflow_policy(rows: List[Dict[str, str]]) -> None:
    if not rows:
        fail('workflow_policy section is empty')
    required = {'Workflow', 'Trigger', 'Required input', 'Required updates', 'Exit rule'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('workflow_policy misses required columns: ' + ', '.join(sorted(missing)))
    longtable(['Workflow', 'Trigger', 'Required input', 'Required updates', 'Exit rule'],
              [0.14, 0.19, 0.18, 0.31, 0.16], rows, 'workflow_policy.tex', r'\small')


def write_pre_implementation_phase_check_policy(rows: List[Dict[str, str]]) -> None:
    if not rows:
        fail('pre_implementation_phase_check_policy section is empty')
    required = {'ID', 'Check status', 'Meaning', 'Required action', 'Ledger effect'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('pre_implementation_phase_check_policy misses required columns: ' + ', '.join(sorted(missing)))
    ids = [str(r.get('ID', '')).strip() for r in rows]
    if len(ids) != len(set(ids)):
        fail('pre_implementation_phase_check_policy contains duplicate IDs')
    allowed = {'G', 'Y', 'O', 'R'}
    seen_status = {str(r.get('Check status', '')).strip() for r in rows}
    if seen_status != allowed:
        fail('pre_implementation_phase_check_policy must define exactly G, Y, O, and R')
    for r in rows:
        rid = str(r.get('ID', '')).strip()
        st = str(r.get('Check status', '')).strip()
        if st not in allowed:
            fail(f'pre_implementation_phase_check_policy row {rid} has invalid Check status {st}; expected G, Y, O, or R')
        for key in required:
            if not str(r.get(key, '')).strip():
                fail(f'pre_implementation_phase_check_policy row {rid} has empty {key}')
    longtable(['ID', 'Check status', 'Meaning', 'Required action', 'Ledger effect'],
              [0.055, 0.065, 0.305, 0.345, 0.190], rows,
              'pre_implementation_phase_check_policy_table.tex', r'\small', {'Check status'}, legend='precheck')
    text = (r'\paragraph{Pre-Implementation Phase Check rule.} This workflow is a forward-looking implementation rehearsal, not a Lean build and not a phase closeout. When requested, the next semantically connected phases are inspected as if they were to be implemented in sequence. The phase-logic colors are: green = already closed/derived-only, yellow = the unique active phase is implementable now, orange = a later phase is implementable only in the derivation chain after listed predecessor closures, red = locked/blocked by missing derived-only prerequisite evidence, and white = non-direct-Lean tooling/refactor/infrastructure/documentation/comparison work. Every red result forces a static finding plus an upstream addressing phase at the natural origin of the missing structure before the blocked phase may become active.' + '\n' + r'\input{tables/pre_implementation_phase_check_policy_table.tex}' + '\n')
    (T / 'pre_implementation_phase_check_policy.tex').write_text(text, encoding='utf-8')




def write_pre_implementation_phase_check_results(rows: List[Dict[str, str]], phase_rows: List[Dict[str, str]]) -> None:
    if not rows:
        fail('pre_implementation_phase_check_results section is empty')
    required = {
        'ID', 'Phase', 'Check status', 'Check mode', 'Implementability scope',
        'Required predecessor closures', 'Assumptions', 'Evidence basis', 'Lean proof risk',
        'Parent/subphase rule', 'Implementability finding', 'Required action',
        'Would generate addressing phase?', 'Generated addressing phase', 'Static findings affected'
    }
    missing = required.difference(rows[0].keys())
    if missing:
        fail('pre_implementation_phase_check_results misses required columns: ' + ', '.join(sorted(missing)))
    ids = [str(r.get('ID', '')).strip() for r in rows]
    if len(ids) != len(set(ids)):
        fail('pre_implementation_phase_check_results contains duplicate IDs')
    phase_ids = {str(r.get('Phase', '')).strip() for r in phase_rows}
    allowed = {'G', 'Y', 'O', 'R'}
    allowed_scope = {'closed', 'now', 'after-listed-predecessors', 'blocked'}
    for r in rows:
        rid = str(r.get('ID', '')).strip()
        phase = str(r.get('Phase', '')).strip()
        st = str(r.get('Check status', '')).strip()
        if not rid:
            fail('pre_implementation_phase_check_results contains a row without ID')
        if phase not in phase_ids:
            fail(f'pre_implementation_phase_check_results row {rid} references unknown phase {phase}')
        if st not in allowed:
            fail(f'pre_implementation_phase_check_results row {rid} has invalid Check status {st}; expected G, Y, O, or R')
        for key in required:
            if not str(r.get(key, '')).strip():
                fail(f'pre_implementation_phase_check_results row {rid} has empty {key}')
        scope = str(r.get('Implementability scope', '')).strip()
        if scope not in allowed_scope:
            fail(f'pre_implementation_phase_check_results row {rid} has invalid Implementability scope {scope}')
        would_generate = str(r.get('Would generate addressing phase?', '')).strip().lower()
        addr = str(r.get('Generated addressing phase', '')).strip().lower()
        if st == 'R':
            if scope != 'blocked':
                fail(f'pre_implementation_phase_check_results row {rid} is red but scope is not blocked')
            if would_generate not in {'yes', 'true'}:
                fail(f'pre_implementation_phase_check_results row {rid} is red but does not require addressing phase generation')
            if addr in {'', 'none', 'none-required', 'not-required'}:
                fail(f'pre_implementation_phase_check_results row {rid} is red but has no generated addressing phase')
        if st == 'Y' and scope != 'now':
            fail(f'pre_implementation_phase_check_results row {rid} is yellow but scope is not now')
        if st == 'O' and scope != 'after-listed-predecessors':
            fail(f'pre_implementation_phase_check_results row {rid} is orange but scope is not after-listed-predecessors')
        if st == 'G' and scope != 'closed':
            fail(f'pre_implementation_phase_check_results row {rid} is green but scope is not closed')
    write_export_tsv('pre_implementation_phase_check_results.generated.tsv', rows)
    summary_rows = []
    for r in rows:
        summary_rows.append({
            'ID': r['ID'],
            'Phase': r['Phase'],
            'Status': r['Check status'],
            'Scope': r['Implementability scope'],
            'Predecessors': r['Required predecessor closures'],
            'Proof risk': r['Lean proof risk'],
            'Addressing?': r['Would generate addressing phase?'],
            'Addressing phase': r['Generated addressing phase'],
        })
    longtable(
        ['ID', 'Phase', 'Status', 'Scope', 'Predecessors', 'Proof risk', 'Addressing?', 'Addressing phase'],
        [0.095, 0.055, 0.040, 0.105, 0.190, 0.250, 0.070, 0.135],
        summary_rows,
        'pre_implementation_phase_check_results_summary_table.tex',
        r'\footnotesize',
        {'Status'},
        legend='precheck'
    )
    lines: List[str] = []
    lines.append(r'\small')
    lines.append(r'\arrayrulecolor{black!22}')
    for r in rows:
        lines.append(r'\phantomsection')
        lines.append(rf'\subsection*{{Pre-check detail {esc(r["ID"])} -- phase {esc(r["Phase"])}}}')
        lines.append(r'\begin{longtable}{L{0.18\linewidth} L{0.78\linewidth}}')
        lines.append(r'\hline')
        lines.append(r'\textbf{Field} & \textbf{Record}\\')
        lines.append(r'\hline')
        for field in ['Check status', 'Check mode', 'Implementability scope', 'Required predecessor closures', 'Assumptions', 'Evidence basis', 'Lean proof risk', 'Parent/subphase rule', 'Implementability finding', 'Required action', 'Would generate addressing phase?', 'Generated addressing phase', 'Static findings affected']:
            lines.append(rf'{esc(field)} & {esc(r.get(field, ""))}\\')
            lines.append(r'\hline\addlinespace[0.20em]')
        lines.append(r'\end{longtable}')
    lines.append(r'\arrayrulecolor{black}')
    lines.append(r'\normalsize')
    (T / 'pre_implementation_phase_check_results_detail_table.tex').write_text('\n'.join(lines) + '\n', encoding='utf-8')
    text = (r'\paragraph{Current pre-implementation phase-window check.} This table records the requested forward-looking thought experiment for the next semantic phase window. It is not a Lean build and does not close any checked phase. Yellow means the unique active phase is implementable now. Orange means a later phase is implementable only in the stated derivation chain after predecessor closures. Red means a Lean-derivation phase is locked/blocked by missing derived-only prerequisite evidence and requires a generated upstream addressing/release proof at the natural origin of the missing structure. White means non-direct-Lean tooling/refactor/infrastructure/documentation/comparison work. Green means already closed/derived-only.' + '\n' + r'\subsection*{Pre-check summary}' + '\n' + r'\input{tables/pre_implementation_phase_check_results_summary_table.tex}' + '\n' + r'\subsection*{Pre-check detail records}' + '\n' + r'\input{tables/pre_implementation_phase_check_results_detail_table.tex}' + '\n')
    (T / 'pre_implementation_phase_check_results.tex').write_text(text, encoding='utf-8')


def write_implementation_scaling_phase_plan(rows: List[Dict[str, str]]) -> None:
    if not rows:
        fail('implementation_scaling_phase_plan section is empty')
    required = {'Phase', 'Name', 'Primary purpose', 'Tool mode', 'Load-control rule', 'Theory semantics', 'Generated artifacts', 'Lean-data effect'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('implementation_scaling_phase_plan misses required columns: ' + ', '.join(sorted(missing)))
    ids = [str(r.get('Phase', '')).strip() for r in rows]
    if len(ids) != len(set(ids)):
        fail('implementation_scaling_phase_plan contains duplicate Phase rows')
    for r in rows:
        ph = str(r.get('Phase', '')).strip()
        if not ph:
            fail('implementation_scaling_phase_plan contains a row without Phase')
        for key in required:
            if not str(r.get(key, '')).strip():
                fail(f'implementation_scaling_phase_plan row {ph} has empty {key}')
    write_export_tsv('implementation_scaling_phase_plan.generated.tsv', rows)
    longtable(
        ['Phase', 'Name', 'Primary purpose', 'Tool mode', 'Load-control rule', 'Theory semantics', 'Generated artifacts', 'Lean-data effect'],
        [0.042, 0.105, 0.195, 0.080, 0.185, 0.190, 0.118, 0.055],
        rows,
        'implementation_scaling_phase_plan_table.tex',
        r'\footnotesize'
    )
    text = (r'\paragraph{Implementation-scaling phase plan.} This table shows how the tool may grow while protecting the Lean/content path. The rows come from the Master YAML and describe Python inventory, generated views, database readiness, context packets, root hygiene and validation surfaces. It is shown to make tooling growth explicit and bounded; none of these scaling rows is an ontic CNNA generator.' + '\n' + r'\input{tables/implementation_scaling_phase_plan_table.tex}' + '\n')
    (T / 'implementation_scaling_phase_plan.tex').write_text(text, encoding='utf-8')

def write_global_no_go_guardrails(rows: List[Dict[str, str]]) -> None:
    if not rows:
        fail('global_no_go_guardrails section is empty')
    required = {'ID', 'Rule', 'Scope', 'Enforcement'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('global_no_go_guardrails misses required columns: ' + ', '.join(sorted(missing)))
    ids = [r.get('ID', '') for r in rows]
    if len(ids) != len(set(ids)):
        fail('global_no_go_guardrails contains duplicate IDs')
    longtable(['ID', 'Rule', 'Scope', 'Enforcement'],
              [0.045, 0.345, 0.185, 0.390], rows, 'global_no_go_guardrails_table.tex', r'\small')
    (T / 'global_no_go_guardrails.tex').write_text(r'''\paragraph{Global no-go guardrail rule.} This table is sourced from the Master YAML guardrail list. The rules below are global repository/workflow invariants, not phase-local suggestions. Every phase scratchpad inherits them through the \texttt{global\_no\_go\_inheritance} field. Phase-local no-go lists are only stricter addenda; they may not weaken, omit, or scope away this table.
\input{tables/global_no_go_guardrails_table.tex}
''', encoding='utf-8')



def write_global_postulates(rows: List[Dict[str, str]]) -> None:
    if not rows:
        fail('global_postulates section is empty')
    required = {'ID', 'Postulate', 'Precise formulation', 'Allowed primitive', 'Derived-only consequences', 'Forbidden primitive imports', 'Enforcement'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('global_postulates misses required columns: ' + ', '.join(sorted(missing)))
    ids = [r.get('ID', '') for r in rows]
    if len(ids) != len(set(ids)):
        fail('global_postulates contains duplicate IDs')
    longtable(['ID', 'Postulate', 'Precise formulation', 'Allowed primitive', 'Derived-only consequences', 'Forbidden primitive imports', 'Enforcement'],
              [0.035, 0.120, 0.310, 0.120, 0.170, 0.140, 0.090], rows, 'global_postulates_table.tex', r'\small')
    text = r'''\paragraph{Global postulate rule.} The postulate below is a global ontology/provenance constraint, not a Lean axiom and not a physical input. It fixes the permitted primitive emergence trigger for the roadmap: subsystem-being inside the formal \texttt{IDEAL\_infty} provenance whole. Everything else must be derived or explicitly marked comparison-only.
\input{tables/global_postulates_table.tex}
'''
    (T / 'global_postulates.tex').write_text(text, encoding='utf-8')



def write_phase_object_link_policy(rows: List[Dict[str, str]]) -> None:
    if not rows:
        fail('phase_object_link_policy section is empty')
    required = {'Kind', 'Meaning', 'Required evidence', 'Rendering rule'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('phase_object_link_policy misses required columns: ' + ', '.join(sorted(missing)))
    kinds = [r.get('Kind', '') for r in rows]
    if len(kinds) != len(set(kinds)):
        fail('phase_object_link_policy contains duplicate kinds')
    expected = {'direct', 'scope_only', 'no_direct_object', 'moved'}
    if set(kinds) != expected:
        fail('phase_object_link_policy must define exactly: ' + ', '.join(sorted(expected)))
    longtable(['Kind', 'Meaning', 'Required evidence', 'Rendering rule'],
              [0.075, 0.245, 0.315, 0.315], rows, 'phase_object_link_policy_table.tex', r'\small')
    (T / 'phase_object_link_policy.tex').write_text(r'''\paragraph{Phase-object-link policy rule.} Direct object ownership is defined only by exact equality \texttt{object.Phase == phase.Phase}. Umbrella phases may display child-object scope for navigation, but child scope does not transfer ownership. A generated phase row may therefore never show an unexplained blank \texttt{Linked objects} cell: it must be rendered as direct links, scope-only child summary, no-direct-object explanation, or moved placeholder.
\input{tables/phase_object_link_policy_table.tex}
''', encoding='utf-8')





def write_context_class_taxonomy(rows: List[Dict[str, str]]) -> None:
    if not rows:
        fail('context_class_taxonomy section is empty')
    required = {'Class', 'Applies to', 'Parent class', 'Meaning', 'Truth role', 'Allowed consumers'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('context_class_taxonomy misses required columns: ' + ', '.join(sorted(missing)))
    classes = [r.get('Class', '') for r in rows]
    if len(classes) != len(set(classes)):
        fail('context_class_taxonomy contains duplicate classes')
    applies = {r.get('Applies to', '') for r in rows}
    if not {'phase', 'object'}.issubset(applies):
        fail('context_class_taxonomy must contain both phase and object classes')
    longtable(['Class', 'Applies to', 'Parent class', 'Meaning', 'Truth role', 'Allowed consumers'],
              [0.115, 0.055, 0.135, 0.245, 0.230, 0.170], rows, 'context_class_taxonomy_table.tex', r'\small')
    (T / 'context_class_taxonomy.tex').write_text(r'''\paragraph{Context-class taxonomy rule.} This table is an orthogonal class/type layer over the phase and object registers. It applies an object-oriented reading to the planning schema: \texttt{Context class} says what kind of entity a row is, while status colors say only release/proof state. A green generated, database, documentation, governance or reference row is therefore not a green Lean object. Conversely, a red Lean derivation phase remains a Lean derivation phase, but blocked by missing derived-only evidence.
\input{tables/context_class_taxonomy_table.tex}
''', encoding='utf-8')


def write_object_significance_taxonomy(rows: List[Dict[str, str]]) -> None:
    if not rows:
        fail('object_significance_taxonomy section is empty')
    required = {'Tier', 'Name', 'Applies to', 'Meaning', 'Documentation requirement', 'Promotion / demotion rule'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('object_significance_taxonomy misses required columns: ' + ', '.join(sorted(missing)))
    tiers = [r.get('Tier', '') for r in rows]
    if tiers != ['F0', 'F1', 'F2', 'F3', 'F4']:
        fail('object_significance_taxonomy must define F0, F1, F2, F3, F4 in order')
    longtable(['Tier', 'Name', 'Applies to', 'Meaning', 'Documentation requirement', 'Promotion / demotion rule'],
              [0.035, 0.060, 0.060, 0.255, 0.310, 0.240], rows, 'object_significance_taxonomy_table.tex', r'\small', set(), {'Tier'})
    (T / 'object_significance_taxonomy.tex').write_text(r'''\paragraph{Object/phase significance-tier rule.} This table is a second orthogonal classification axis. \texttt{Context class} says what a row is; \texttt{Significance tier} / \texttt{Phase documentation tier} says how deep the proof/documentation burden is. It is deliberately independent of status and class: a reference gate may be high-significance, and a Lean-facing helper may be auxiliary. Trivial rows stay visible without bloating the proofbook; fundamental rows must receive full dossiers before public-final promotion or downstream consumption.
\input{tables/object_significance_taxonomy_table.tex}
''', encoding='utf-8')



def write_lean_declaration_classification_taxonomy(rows: List[Dict[str, str]]) -> None:
    if not rows:
        fail('lean_declaration_classification_taxonomy section is empty')
    required = {'Axis', 'Code', 'Name', 'Meaning', 'Assignment rule', 'Closure rule'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('lean_declaration_classification_taxonomy misses required columns: ' + ', '.join(sorted(missing)))
    seen: Set[Tuple[str, str]] = set()
    axes: Set[str] = set()
    for r in rows:
        axis = str(r.get('Axis', '')).strip()
        code = str(r.get('Code', '')).strip()
        if not axis or not code:
            fail('lean_declaration_classification_taxonomy row has empty Axis or Code')
        key = (axis, code)
        if key in seen:
            fail(f'lean_declaration_classification_taxonomy duplicate row {axis}/{code}')
        seen.add(key)
        axes.add(axis)
        for col in required:
            if not str(r.get(col, '')).strip():
                fail(f'lean_declaration_classification_taxonomy row {axis}/{code} has empty {col}')
    required_axes = {'declaration_kind', 'semantic_role', 'triviality_tier', 'documentation_requirement', 'lifecycle_state', 'public_surface_status'}
    missing_axes = required_axes.difference(axes)
    if missing_axes:
        fail('lean_declaration_classification_taxonomy misses required axes: ' + ', '.join(sorted(missing_axes)))
    sentinels = {
        ('declaration_kind', 'unknown-manual-review'),
        ('semantic_role', 'unknown-manual-review'),
        ('triviality_tier', 'T?'),
        ('documentation_requirement', 'manual-review-required'),
        ('lifecycle_state', 'unknown-manual-review'),
        ('public_surface_status', 'manual-review-required'),
    }
    missing_sentinels = sentinels.difference(seen)
    if missing_sentinels:
        fail('lean_declaration_classification_taxonomy misses unresolved/manual-review blocker sentinels: ' + ', '.join(f'{a}/{c}' for a, c in sorted(missing_sentinels)))
    longtable(['Axis', 'Code', 'Name', 'Meaning', 'Assignment rule', 'Closure rule'],
              [0.105, 0.095, 0.110, 0.255, 0.215, 0.185], rows, 'lean_declaration_classification_taxonomy_table.tex', r'\footnotesize')
    text = r"""\paragraph{Lean declaration total-classification rule.} This table is the required classification vocabulary for the full Lean declaration surface, not merely for the curated object register. A declaration consumption class is not enough. Before LEG37/CEX0/Phase 21.0 can close, every current Lean declaration must have one syntactic declaration kind, one semantic role, one triviality tier, one documentation requirement, one lifecycle state, one public-surface status, and one owning CNNA object or explicit non-object bucket. Automatic scanner results are candidate labels only: \texttt{rfl}, projection shape, declaration keyword, path, and reference count cannot by themselves decide triviality or significance. Manual/curated override is mandatory whenever a syntactically trivial declaration carries handoff, boundary, public API, or fundamental definitional semantics.
\input{tables/lean_declaration_classification_taxonomy_table.tex}
"""
    (T / 'lean_declaration_classification_taxonomy.tex').write_text(text, encoding='utf-8')

def write_reuse_duplication_ledger(rows: List[Dict[str, str]]) -> None:
    if not rows:
        fail('reuse_duplication_ledger section is empty')
    required = {'ID', 'Scope', 'Existing canonical seam', 'Decision', 'Allowed action', 'Blocked duplication', 'Evidence', 'Future consumers'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('reuse_duplication_ledger misses required columns: ' + ', '.join(sorted(missing)))
    ids = [r.get('ID', '') for r in rows]
    if len(ids) != len(set(ids)):
        fail('reuse_duplication_ledger contains duplicate IDs')
    allowed_decisions = {
        'consume_or_extend_existing',
        'consume_existing_mainline',
        'genuine_semantic_split_already_existing',
        'artifact_only_split',
        'artifact_only_audit_not_ontic_generator',
        'future_consume_or_wrap_canonical_generator',
        'defer_until_code_phase_proves_need',
        'genuine_semantic_split_required',
    }
    for r in rows:
        dec = str(r.get('Decision', '')).strip()
        if dec not in allowed_decisions:
            fail(f'reuse_duplication_ledger row {r.get("ID", "?")} has invalid Decision {dec}')
        if not str(r.get('Blocked duplication', '')).strip():
            fail(f'reuse_duplication_ledger row {r.get("ID", "?")} lacks blocked-duplication rule')
    lines: List[str] = []
    lines.append(r'\small')
    lines.append(r'\arrayrulecolor{black!22}')
    for r in rows:
        rid = str(r.get('ID', ''))
        title = str(r.get('Scope', ''))
        lines.append(r'\phantomsection')
        lines.append(rf'\subsection*{{Reuse ledger row {esc(rid)} -- {esc(title)}}}')
        lines.append(r'\begin{longtable}{L{0.16\linewidth} L{0.81\linewidth}}')
        lines.append(r'\hline')
        lines.append(r'\textbf{Field} & \textbf{Record}\\')
        lines.append(r'\hline')
        fields = ['ID', 'Scope', 'Existing canonical seam', 'Decision', 'Allowed action', 'Blocked duplication', 'Evidence', 'Future consumers']
        for field in fields:
            lines.append(rf'{esc(field)} & {esc(r.get(field, ""))}\\')
            lines.append(r'\hline\addlinespace[0.20em]')
        lines.append(r'\end{longtable}')
    lines.append(r'\arrayrulecolor{black}')
    lines.append(r'\normalsize')
    (T / 'reuse_duplication_ledger_table.tex').write_text('\n'.join(lines) + '\n', encoding='utf-8')
    text = "\\paragraph{Reuse and duplication ledger rule.} This generated view closes LEG11 as a planning/API hygiene contract. It is not a Lean source and not a mathematical generator. A future generator-like implementation must be classified here before code is added: consume an existing seam, extend it at its natural source layer, wrap it for import/API reasons, or record a genuine semantic split. Parallel request/output, extraction, ledger, smoke-test, or theory-generation paths are blocked by default.\n\\input{tables/reuse_duplication_ledger_table.tex}\n"
    (T / 'reuse_duplication_ledger.tex').write_text(text, encoding='utf-8')


def write_consumption_classification_map(policy_rows: List[Dict[str, str]], obj_rows: List[Dict[str, str]], dossier_rows: List[Dict[str, str]]) -> None:
    if not policy_rows:
        fail('consumption_classification_map section is empty')
    required = {'Class', 'Meaning', 'Evidence rule', 'Public/API disposition', 'Blocked promotion rule'}
    missing = required.difference(policy_rows[0].keys())
    if missing:
        fail('consumption_classification_map misses required columns: ' + ', '.join(sorted(missing)))
    allowed_classes = {
        'core-computational',
        'proof-bridge',
        'public-wrapper',
        'legacy-status',
        'legacy-policy',
        'phase-alias',
        'audit-only',
        'blue-semantic-correction',
        'dead-candidate',
        'final-output',
    }
    classes = [str(r.get('Class', '')).strip() for r in policy_rows]
    if len(classes) != len(set(classes)):
        fail('consumption_classification_map contains duplicate Class values')
    if set(classes) != allowed_classes:
        fail('consumption_classification_map must define exactly: ' + ', '.join(sorted(allowed_classes)))
    for r in policy_rows:
        for key in required:
            if not str(r.get(key, '')).strip():
                fail(f'consumption_classification_map class {r.get("Class", "?")} has empty {key}')

    inventory_path = ROOT / 'repo_inventory/raw_export/modules.json'
    declarations_path = ROOT / 'repo_inventory/raw_export/symbol_references/declarations.json'
    references_path = ROOT / 'repo_inventory/raw_export/symbol_references/references.json'
    sink_taxonomy_path = ROOT / 'repo_inventory/raw_export/architectural_core/sink_taxonomy.json'
    for path in (inventory_path, declarations_path, references_path):
        if not path.exists():
            fail(f'consumption classification requires {path.relative_to(ROOT)}')

    inventory = json.loads(inventory_path.read_text(encoding='utf-8'))
    declarations = json.loads(declarations_path.read_text(encoding='utf-8'))
    references = json.loads(references_path.read_text(encoding='utf-8'))
    sink_taxonomy = json.loads(sink_taxonomy_path.read_text(encoding='utf-8')) if sink_taxonomy_path.exists() else {'entries': []}

    module_entries = inventory.get('modules', [])
    if not isinstance(module_entries, list) or not module_entries:
        fail('repo_inventory/raw_export/modules.json has no module list')
    sink_class_by_module = {str(e.get('module', '')): str(e.get('classification', '')) for e in sink_taxonomy.get('entries', []) if isinstance(e, dict)}
    reference_consumer_counts: Dict[str, int] = {}
    reference_consumers: Dict[str, List[str]] = {}
    for edge in references.get('edges', []):
        dep = str(edge.get('dependency_module', ''))
        con = str(edge.get('consumer_module', ''))
        if dep:
            reference_consumer_counts[dep] = reference_consumer_counts.get(dep, 0) + int(edge.get('reference_count', 0) or 0)
            reference_consumers.setdefault(dep, [])
            if con and con not in reference_consumers[dep]:
                reference_consumers[dep].append(con)

    def name_has_phase_alias(text: str) -> bool:
        return re.search(r'(?<![A-Za-z0-9])SM[0-9][A-Za-z0-9_]*|SM[0-9]', text) is not None

    def classify_module(entry: Dict[str, Any]) -> Tuple[str, str]:
        module = str(entry.get('module', ''))
        path = str(entry.get('path', ''))
        group = str(entry.get('group', ''))
        leaf = module.rsplit('.', 1)[-1]
        text = ' '.join([module, path, group, leaf]).lower()
        if entry.get('is_build_module') or leaf in {'BuildAll'} or module in {'CNNA.PillarA', 'CNNA.PillarB', 'CNNA.PillarC', 'CNNA.PillarD', 'CNNA.PillarE'}:
            return 'public-wrapper', 'build/umbrella module wrapper; wrapper is not semantic final proof evidence'
        if entry.get('is_notation_module'):
            return 'legacy-policy', 'notation/control module; public syntax surface, not a mathematical generator'
        if any(k in text for k in ['nogo', 'no_go', 'no-go', 'obstruction', 'blocked', 'dead', 'impossible', 'negative']):
            return 'dead-candidate', 'name/path marks a rejected, blocked, negative, or obstruction route'
        if 'legacy' in text or re.search(r'\bstatus\b|statusgate|statusgates', text):
            return 'legacy-status', 'status/legacy gate marker; quarantine before public consumption'
        if any(k in text for k in ['policy', 'ledger', 'decision', 'format', 'audit', 'inventory', 'contract', 'report']):
            return 'legacy-policy', 'policy/ledger/audit module; governance evidence, not ontic CNNA input'
        if name_has_phase_alias(module) or '/Smoke/' in path or '.Smoke.' in module:
            return 'phase-alias', 'phase/smoke-test namespace carries implementation-history aliases'
        if sink_class_by_module.get(module) == 'intentional_output':
            return 'final-output', 'architectural sink taxonomy marks module as intentional output'
        if any(k in text for k in ['proof', 'certificate', 'bridge', 'correctness', 'identity']):
            return 'proof-bridge', 'module name carries certificate/proof/bridge/identity role'
        if module.startswith('CNNA.PillarA'):
            return 'core-computational', 'Pillar-A internal module without policy/wrapper/phase/dead markers'
        return 'audit-only', 'non-Pillar-A or unclassified module; keep as read-only audit surface'

    def classify_declaration(module_class: str, module_evidence: str, decl: Dict[str, Any]) -> Tuple[str, str]:
        raw = str(decl.get('raw_name', ''))
        full = str(decl.get('full_name', ''))
        base = str(decl.get('basename', raw))
        text = ' '.join([raw, full, base]).lower()
        if any(k in text for k in ['nogo', 'no_go', 'no-go', 'obstruction', 'blocked', 'dead', 'impossible', 'negative']):
            return 'dead-candidate', 'declaration name marks a blocked/negative/obstruction route'
        if 'legacy' in text or re.search(r'\bstatus\b|statusgate|statusgates', text):
            return 'legacy-status', 'declaration is a legacy/status marker'
        if any(k in text for k in ['policy', 'ledger', 'decision', 'format', 'audit', 'inventory', 'contract', 'report']):
            return 'legacy-policy', 'declaration is governance/policy/ledger/audit material'
        if name_has_phase_alias(full):
            return 'phase-alias', 'declaration name contains phase/smoke alias marker'
        if any(k in text for k in ['proof', 'certificate', 'correctness', 'identity', 'twosidedinv', 'two_sided', 'verified', 'witness', '_eq']):
            return 'proof-bridge', 'declaration name carries proof/certificate/equality/witness role'
        return module_class, 'inherits module classification: ' + module_evidence

    module_records: List[Dict[str, str]] = []
    declaration_records: List[Dict[str, str]] = []
    class_counts_modules: Counter = Counter()
    class_counts_decls: Counter = Counter()
    module_class_by_name: Dict[str, str] = {}
    module_evidence_by_name: Dict[str, str] = {}
    module_path_by_name: Dict[str, str] = {}
    for entry in module_entries:
        module = str(entry.get('module', ''))
        path = str(entry.get('path', ''))
        cls, evidence = classify_module(entry)
        module_class_by_name[module] = cls
        module_evidence_by_name[module] = evidence
        module_path_by_name[module] = path
        consumer_modules = reference_consumers.get(module, [])
        record = {
            'Module': module,
            'Path': path,
            'Group': str(entry.get('group', '')),
            'Consumption class': cls,
            'Classification evidence': evidence,
            'Imported-by count': str(len(entry.get('internal_imported_by', []) or [])),
            'Reference consumer count': str(reference_consumer_counts.get(module, 0)),
            'Reference consumer sample': '; '.join(consumer_modules[:5]),
            'Public promotion gate': 'not public-final unless an object proof dossier and public API contract later permit it',
        }
        module_records.append(record)
        class_counts_modules[cls] += 1

    decl_modules = declarations.get('modules', {})
    if not isinstance(decl_modules, dict):
        fail('symbol_references/declarations.json modules must be a mapping')
    for module, rec in decl_modules.items():
        decls = rec.get('declarations', []) if isinstance(rec, dict) else []
        if not isinstance(decls, list):
            fail(f'declarations for module {module} are not a list')
        mcls = module_class_by_name.get(module, 'audit-only')
        mev = module_evidence_by_name.get(module, 'module absent from module inventory')
        for decl in decls:
            dcls, dev = classify_declaration(mcls, mev, decl)
            reference_consumer_sample = '; '.join(reference_consumers.get(module, [])[:5])
            declaration_records.append({
                'Module': str(module),
                'Path': module_path_by_name.get(str(module), ''),
                'Line': str(decl.get('line', '')),
                'Declaration': str(decl.get('full_name', decl.get('raw_name', ''))),
                'Basename': str(decl.get('basename', '')),
                'Consumption class': dcls,
                'Classification evidence': dev,
                'Module class': mcls,
                'Reference consumer count': str(reference_consumer_counts.get(str(module), 0)),
                'Reference consumer sample': reference_consumer_sample,
                'Public promotion gate': 'blocked from public-final unless later linked to a documented object/API contract',
            })
            class_counts_decls[dcls] += 1

    dossier_by_id = {str(r.get('ID', '')): r for r in dossier_rows}
    object_records: List[Dict[str, str]] = []
    class_counts_objects: Counter = Counter()
    for obj in obj_rows:
        oid = str(obj.get('ID', ''))
        status = str(obj.get('Object status', ''))
        layer = str(obj.get('Layer', '')).lower()
        proof_status = str(obj.get('Proof documentation status', ''))
        dossier = dossier_by_id.get(oid, {})
        if status == 'B':
            cls = 'blue-semantic-correction'
            evidence = 'object register status B; semantic/API correction required before any public-final use'
        elif status in {'R', 'K'}:
            cls = 'dead-candidate'
            evidence = f'object register status {status}; blocked/quarantined until a later ledger changes it'
        elif 'planning' in layer or 'governance' in layer or 'legacy' in layer:
            cls = 'legacy-policy'
            evidence = 'object layer is planning/governance/legacy control surface'
        elif status == 'G' and str(dossier.get('Documented', '')).strip().lower() in {'yes', 'yes-infrastructure', 'documented'}:
            cls = 'final-output'
            evidence = 'green object with documented dossier; still subject to public API contract if exported'
        else:
            cls = 'core-computational'
            evidence = 'registered object is not green-final and not blue/quarantined; keep internal until its own phase closes'
        if status == 'B' and cls in {'final-output', 'public-wrapper'}:
            fail(f'blue object {oid} was classified as public/final')
        object_records.append({
            'Object ID': oid,
            'Object': str(obj.get('Object', '')),
            'Phase': str(obj.get('Phase', '')),
            'Object status': status,
            'Proof documentation status': proof_status,
            'Proof dossier': str(obj.get('Proof dossier', '')),
            'Consumption class': cls,
            'Classification evidence': evidence,
            'Public promotion gate': 'blue objects are blocked; all public exports additionally require proof dossier and public API contract',
        })
        class_counts_objects[cls] += 1

    write_export_tsv('consumption_classification_map.generated.tsv', policy_rows)
    write_export_tsv('module_consumption_records.generated.tsv', module_records)
    write_export_tsv('declaration_consumption_records.generated.tsv', declaration_records)
    write_export_tsv('object_consumption_classification.generated.tsv', object_records)

    summary_rows: List[Dict[str, str]] = []
    for cls in sorted(allowed_classes):
        summary_rows.append({
            'Class': cls,
            'Modules': str(class_counts_modules.get(cls, 0)),
            'Declarations': str(class_counts_decls.get(cls, 0)),
            'Objects': str(class_counts_objects.get(cls, 0)),
            'Public/API disposition': next(r['Public/API disposition'] for r in policy_rows if r['Class'] == cls),
        })
    longtable(['Class', 'Meaning', 'Evidence rule', 'Public/API disposition', 'Blocked promotion rule'],
              [0.115, 0.245, 0.230, 0.190, 0.180], policy_rows, 'consumption_classification_map_policy_table.tex', r'\footnotesize')
    longtable(['Class', 'Modules', 'Declarations', 'Objects', 'Public/API disposition'],
              [0.135, 0.060, 0.075, 0.060, 0.620], summary_rows, 'consumption_classification_map_summary_table.tex', r'\footnotesize')
    text = r'''\paragraph{Declaration consumption classification rule.} LEG5 is a generated planning/API-hygiene artifact, not a Lean source and not a mathematical generator. The classifier distinguishes semantic consumption from mere BuildAll/import reachability. Full module-, declaration-, and object-level records are exported as TSV files; the PDF renders only the class policy and aggregate counts to avoid turning the roadmap into an unreadable declaration dump.
\input{tables/consumption_classification_map_policy_table.tex}
\subsection*{Generated classification counts}
\input{tables/consumption_classification_map_summary_table.tex}
\paragraph{Promotion gate.} A blue object is always classified as \texttt{blue-semantic-correction}. It cannot become \texttt{final-output} or \texttt{public-wrapper} from proof-carrying code alone; later phases must close the semantic correction ledger, proof dossier, and public API contract.
'''
    (T / 'consumption_classification_map.tex').write_text(text, encoding='utf-8')


def write_secondary_long_term_goals(rows: List[Dict[str, str]]) -> None:
    if not rows:
        return
    required = {'ID', 'Goal', 'Motivation', 'Vision', 'Raw data / tools', 'Operational scope', 'Not-before gate', 'Derived-only boundary', 'Plan action'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('secondary_long_term_goals misses required columns: ' + ', '.join(sorted(missing)))
    ids = [r.get('ID', '') for r in rows]
    if len(ids) != len(set(ids)):
        fail('secondary_long_term_goals contains duplicate IDs')
    longtable(
        ['ID', 'Goal', 'Motivation', 'Vision', 'Raw data / tools', 'Operational scope', 'Not-before gate', 'Derived-only boundary', 'Plan action'],
        [0.040, 0.105, 0.135, 0.145, 0.120, 0.115, 0.115, 0.120, 0.075],
        rows,
        'secondary_long_term_goals_table.tex',
        r'\footnotesize'
    )
    (T / 'secondary_long_term_goals.tex').write_text(
        r'''\paragraph{Secondary long-term goal rule.} The goals below are secondary to Lean implementation, but not all are purely downstream. The Vision column records motivating long-horizon interface and review ambitions without upgrading them to CNNA inputs. When a goal is marked as immediate-principles, its epistemic/governance constraints apply now while its technical implementation may remain later. These goals may use generated repository metadata, proof dossiers, derivation graphs, review records, context-documentation slices, and future database exports as documentation or diagnostic material, but they do not supply CNNA-generative data. They must not displace the active Phase-1 cleanup, computable-instance traversal, or derived-only object closure.
\input{tables/secondary_long_term_goals_table.tex}
''',
        encoding='utf-8'
    )

def write_external_source_crosscheck(rows: List[Dict[str, str]]) -> None:
    if not rows:
        return
    required = {
        'ID', 'Topic', 'Thread evidence', 'External check', 'Plan disposition',
        'CNNA action', 'Phase/Object', 'Risk / uncertainty'
    }
    missing = required.difference(rows[0].keys())
    if missing:
        fail('external_source_crosscheck misses required columns: ' + ', '.join(sorted(missing)))
    longtable(
        ['ID', 'Topic', 'Source evidence', 'External check', 'Plan disposition', 'CNNA action', 'Phase/Object', 'Risk / uncertainty'],
        [0.040, 0.105, 0.160, 0.130, 0.125, 0.165, 0.075, 0.135],
        [{**r, 'Source evidence': r.get('Thread evidence', '')} for r in rows],
        'external_source_crosscheck_table.tex',
        r'\footnotesize'
    )
    (T / 'external_source_crosscheck.tex').write_text(
        r'''\paragraph{Source-integration rule.} This is an external-reference and legacy-roadmap audit only. TomS thread material, uploaded roadmap material and public mathematical references may define comparison targets, warning signs, migration duties and proof obligations, but they do not supply CNNA-generative data. Every accepted action below is therefore routed through existing or newly added derived-only phases and object records.
\input{tables/external_source_crosscheck_table.tex}
''',
        encoding='utf-8'
    )

    # Backward-compatible aliases for older generated full documents.
    (T / 'toms_thread_crosscheck_table.tex').write_text((T / 'external_source_crosscheck_table.tex').read_text(encoding='utf-8'), encoding='utf-8')
    (T / 'toms_thread_crosscheck.tex').write_text((T / 'external_source_crosscheck.tex').read_text(encoding='utf-8'), encoding='utf-8')



def object_proof_label(obj_id: str) -> str:
    return 'objproof:' + str(obj_id).replace('.', '-')


def object_proof_id_cell(obj_id: str, target: bool = False) -> str:
    oid = esc(obj_id)
    if target:
        return rf'\hypertarget{{{object_proof_label(obj_id)}}}{{\textbf{{{oid}}}}}'
    return rf'\hyperlink{{{object_proof_label(obj_id)}}}{{{oid}}}'


def validate_object_proof_dossiers(dossier_rows: List[Dict[str, str]], obj_rows: List[Dict[str, str]]) -> None:
    if not dossier_rows:
        fail('object_proof_dossiers section is empty')
    required = {'ID', 'Object', 'Phase', 'Documented', 'Source objects', 'Definitions', 'Proof target', 'Proof sketch', 'Verification / audit', 'Next documentation action', 'Significance tier', 'Documentation depth requirement'}
    obj_by_id = {r['ID']: r for r in obj_rows}
    obj_ids = set(obj_by_id)
    dossier_ids = [r.get('ID', '').strip() for r in dossier_rows]
    if len(dossier_ids) != len(set(dossier_ids)):
        fail('object_proof_dossiers contains duplicate IDs')
    missing_dossiers = obj_ids.difference(dossier_ids)
    extra = set(dossier_ids).difference(obj_ids)
    if missing_dossiers:
        fail('object_proof_dossiers misses object IDs: ' + ', '.join(sorted(missing_dossiers)))
    if extra:
        fail('object_proof_dossiers contains IDs not in object register: ' + ', '.join(sorted(extra)))
    for idx, row in enumerate(dossier_rows):
        missing = required.difference(row.keys())
        if missing:
            fail(f'object_proof_dossiers row {idx} misses required columns: ' + ', '.join(sorted(missing)))
        oid = row['ID'].strip()
        for key in required:
            if not str(row.get(key, '')).strip():
                fail(f'object_proof_dossiers row {oid} has empty required field {key}')
        obj = obj_by_id[oid]
        if row['Object'].strip() != obj.get('Object', '').strip():
            fail(f'object_proof_dossiers row {oid} Object does not match object register')
        if row['Phase'].strip() != obj.get('Phase', '').strip():
            fail(f'object_proof_dossiers row {oid} Phase does not match object register')


def write_object_proof_documentation(dossier_rows: List[Dict[str, str]], obj_rows: List[Dict[str, str]]) -> None:
    obj_phase = {r['ID']: r.get('Phase', '') for r in obj_rows}
    obj_status = {r['ID']: r.get('Object status', '') for r in obj_rows}
    obj_context = {r['ID']: r.get('Context class', '') for r in obj_rows}
    obj_tier = {r['ID']: r.get('Significance tier', '') for r in obj_rows}
    obj_doc_req = {r['ID']: r.get('Documentation depth requirement', '') for r in obj_rows}
    obj_lifecycle = {r['ID']: r.get('Object lifecycle state', '') for r in obj_rows}
    obj_lifecycle_successor = {r['ID']: r.get('Lifecycle successor/current object', '') for r in obj_rows}
    obj_current_dossier = {r['ID']: r.get('Current dossier pointer', '') for r in obj_rows}
    obj_lifecycle_note = {r['ID']: r.get('Lifecycle note', '') for r in obj_rows}
    lines: List[str] = []
    lines.append(r'\paragraph{Object and quantities proof-documentation workflow.} This section is generated from the object proof-dossier records in the Master YAML. It is the proofbook infrastructure. Every registered object or quantity has an object-owned dossier. Phase scratchpads remain phase-owned implementation records; object lifecycle fields preserve non-destructive patch, rename, deletion and supersession history. A dossier is not automatically a Lean proof; it records the source objects, definition, proof target, proof sketch, lifecycle status and verification status that must be checked against code. Blue objects may be proof-carrying yet semantically/API-unfinished; their dossier must state that gap before any public-final promotion.')
    lines.append('')
    lines.append(r'\small')
    lines.append(r'\arrayrulecolor{black!22}')
    for r in dossier_rows:
        oid = r['ID']
        phase = obj_phase.get(oid, r.get('Phase', '')).strip()
        title = r.get('Object', '')
        lines.append(r'\phantomsection')
        lines.append(rf'\subsection*{{Object or quantity {esc(oid)} -- {esc(title)}}}')
        lines.append(rf'\hypertarget{{{object_proof_label(oid)}}}{{}}')
        lines.append(table_legend_tex('object'))
        lines.append(r'\begin{longtable}{L{0.16\linewidth} L{0.81\linewidth}}')
        lines.append(r'\hline')
        lines.append(r'\textbf{Field} & \textbf{Record}\\')
        lines.append(r'\hline')
        dossier_fields = [
            ('Object ID', object_table_id_cell(oid, target=False), True),
            ('Object status', status_cell(obj_status.get(oid, '')), True),
            ('Context class', esc(obj_context.get(oid, '')), True),
            ('Significance tier', esc(obj_tier.get(oid, '')), True),
            ('Documentation depth requirement', esc(obj_doc_req.get(oid, '')), True),
            ('Documented', esc(r.get('Documented', '')), True),
            ('Object lifecycle state', esc(obj_lifecycle.get(oid, '')), True),
            ('Lifecycle successor/current object', esc(obj_lifecycle_successor.get(oid, '')), True),
            ('Current dossier pointer', esc(obj_current_dossier.get(oid, '')), True),
            ('Lifecycle note', esc(obj_lifecycle_note.get(oid, '')), True),
            ('Phase', phase_link_cell(phase), True),
            ('Source objects', esc(r.get('Source objects', '')), False),
            ('Definitions', esc(r.get('Definitions', '')), False),
            ('Proof target', esc(r.get('Proof target', '')), False),
            ('Proof sketch', esc(r.get('Proof sketch', '')), False),
            ('Verification / audit', esc(r.get('Verification / audit', '')), False),
            ('Next documentation action', esc(r.get('Next documentation action', '')), False),
        ]
        for key, val, raw in dossier_fields:
            lines.append(rf'{esc(key)} & {val}\\')
            lines.append(r'\hline\addlinespace[0.20em]')
        lines.append(r'\end{longtable}')
    lines.append(r'\arrayrulecolor{black}')
    lines.append(r'\normalsize')
    (T / 'object_proof_documentation.tex').write_text('\n'.join(lines) + '\n', encoding='utf-8')


def write_object_tables(obj_rows: List[Dict[str, str]]) -> None:
    rows_a = []
    rows_b = []
    rows_c = []
    rows_d = []
    for r in obj_rows:
        ra, rb, rc, rd = dict(r), dict(r), dict(r), dict(r)
        ra['ID'] = object_table_id_cell(r['ID'], target=True)
        rb['ID'] = object_table_id_cell(r['ID'], target=False)
        rc['ID'] = object_table_id_cell(r['ID'], target=False)
        rd['ID'] = object_table_id_cell(r['ID'], target=False)
        rd['Proof dossier'] = object_proof_id_cell(r['ID'], target=False)
        for rr in (ra, rb, rc, rd):
            rr['Context class'] = context_class_cell(r.get('Context class', ''))
            rr['Significance tier'] = esc(r.get('Significance tier', ''))
            rr['Tier'] = esc(r.get('Significance tier', ''))
            rr['Object lifecycle state'] = esc(r.get('Object lifecycle state', ''))
            rr['Lifecycle'] = esc(r.get('Object lifecycle state', ''))
            rr['Lifecycle successor/current object'] = esc(r.get('Lifecycle successor/current object', ''))
            rr['Successor/current'] = esc(r.get('Lifecycle successor/current object', ''))
            rr['Current dossier pointer'] = esc(r.get('Current dossier pointer', ''))
            rr['Lifecycle note'] = esc(r.get('Lifecycle note', ''))
        rd['Change version'] = str(r.get('Change version', 'unchanged-by-V1.01'))
        rd['Change timestamp'] = str(r.get('Change timestamp', 'Lean data ' + r.get('Data timestamp', '2026-05-10T05:51:42+02:00')))
        for rr in (ra, rb, rc, rd):
            rr['Phase'] = phase_link_cell(r.get('Phase', '').strip())
        rows_a.append(ra); rows_b.append(rb); rows_c.append(rc); rows_d.append(rd)
    longtable(['ID', 'Object', 'Context class', 'Tier', 'Lifecycle', 'Layer', 'Object status', 'Code status', 'Current code modules / derivation site', 'Neutral target location / canonical API', 'Phase'],
              [0.022, 0.086, 0.063, 0.032, 0.044, 0.048, 0.028, 0.070, 0.247, 0.205, 0.022], rows_a, 'object_module_register.tex', r'\footnotesize', {'Object status'}, {'ID', 'Phase', 'Context class'}, legend='object')
    longtable(['ID', 'Object', 'Context class', 'Tier', 'Lifecycle', 'Object status', 'Canonical CNNA definition', 'Natural provenance', 'Computed from', 'ExecComplex/computable path', 'Priority', 'Phase'],
              [0.022, 0.082, 0.065, 0.032, 0.042, 0.028, 0.180, 0.145, 0.115, 0.145, 0.042, 0.022], rows_b, 'object_derivation_register.tex', r'\footnotesize', {'Object status'}, {'ID', 'Phase', 'Context class'}, legend='object')
    longtable(['ID', 'Object', 'Context class', 'Tier', 'Lifecycle', 'Object status', 'Pillar-A access', 'Handoff rights', 'May be consumed by', 'Current code modules / derivation site', 'Phase'],
              [0.022, 0.064, 0.063, 0.032, 0.040, 0.026, 0.135, 0.115, 0.110, 0.300, 0.022], rows_c, 'object_access_register.tex', r'\footnotesize', {'Object status'}, {'ID', 'Phase', 'Context class'}, legend='object')
    longtable(['ID', 'Object', 'Context class', 'Tier', 'Lifecycle', 'Successor/current', 'Object status', 'Proof documentation status', 'Documentation depth requirement', 'Proof dossier', 'Current dossier pointer', 'Change version', 'Change timestamp', 'Phase'],
              [0.020, 0.078, 0.058, 0.028, 0.038, 0.050, 0.024, 0.058, 0.190, 0.045, 0.050, 0.052, 0.076, 0.020], rows_d, 'object_proof_link_register.tex', r'\footnotesize', {'Object status'}, {'ID', 'Proof dossier', 'Phase', 'Context class'}, legend='object')
    (T / 'object_register.tex').write_text(r'''\paragraph{Object register rule.} This section renders object-to-code, context class, derivation, access, handoff rights, lifecycle state, successor/current-object pointers, and proof-documentation links from the Single YAML Master. It is shown because phase release must cite registered derived-only objects rather than relying on informal intent. Context class separates Lean objects from tool, generated, database, documentation, governance and reference-gate objects; Significance tier controls the documentation burden from F0 full dossier to F4 mention-only; object status remains release/proof-state only; object lifecycle state records whether an object row is current, superseded, renamed-alias or deleted-retired. Historical object rows are retained and point to successor/current dossiers instead of being overwritten. Legends are local to the object tables that carry colored object-status cells.
\subsection*{Object table A: current code modules}
\input{tables/object_module_register.tex}
\subsection*{Object table B: derivation, Exec path, and status}
\input{tables/object_derivation_register.tex}
\subsection*{Object table C: access, handoff, and consumer rights}
\input{tables/object_access_register.tex}
\subsection*{Object table D: proof-documentation status and proofbook links}
\input{tables/object_proof_link_register.tex}
''', encoding='utf-8')


def write_scratchpad(scratch_rows: List[Dict[str, Any]], phase_rows: List[Dict[str, str]]) -> None:
    phase_status = {r['Phase']: r['Phase status'] for r in phase_rows}
    phase_title = {r['Phase']: r['Main goal'] for r in phase_rows}
    phase_context = {r['Phase']: r.get('Context class', '') for r in phase_rows}
    phase_doc_tier = {r['Phase']: r.get('Phase documentation tier', '') for r in phase_rows}
    phase_doc_req = {r['Phase']: r.get('Phase documentation depth requirement', '') for r in phase_rows}
    scratch_by = {str(r['phase_id']): r for r in scratch_rows}
    ordered = [scratch_by[ph] for ph in phase_status if ph in scratch_by]
    with (T / 'implementation_scratchpad.tex').open('w', encoding='utf-8') as f:
        f.write(r'\small' + '\n')
        f.write(r'\arrayrulecolor{black!22}' + '\n')
        for r in ordered:
            phase = str(r['phase_id'])
            f.write(r'\phantomsection' + '\n')
            f.write(rf'\subsection*{{Phase {esc(phase)} -- {esc(phase_title.get(phase, r.get("title", "")))}}}' + '\n')
            f.write(rf'\label{{{phase_label(phase)}}}' + '\n')
            f.write(table_legend_tex('phase') + '\n')
            f.write(r'\begin{longtable}{L{0.16\linewidth} L{0.81\linewidth}}' + '\n')
            f.write(r'\hline' + '\n')
            f.write(r'\textbf{Field} & \textbf{Record}\\' + '\n')
            f.write(r'\hline' + '\n')
            f.write(rf'Phase status & {status_cell(phase_status[phase])}\\' + '\n')
            f.write(r'\hline\addlinespace[0.20em]' + '\n')
            f.write(rf'Context class & {esc(phase_context.get(phase, ""))}\\' + '\n')
            f.write(r'\hline\addlinespace[0.20em]' + '\n')
            f.write(rf'Phase documentation tier & {esc(phase_doc_tier.get(phase, ""))}\\' + '\n')
            f.write(r'\hline\addlinespace[0.20em]' + '\n')
            f.write(rf'Phase documentation depth requirement & {esc(phase_doc_req.get(phase, ""))}\\' + '\n')
            f.write(r'\hline\addlinespace[0.20em]' + '\n')
            f.write(rf'Record change version & {esc(str(r.get("Change version", "unchanged-by-V1.01")))}\\' + '\n')
            f.write(r'\hline\addlinespace[0.20em]' + '\n')
            f.write(rf'Record change timestamp & {esc(str(r.get("Change timestamp", "Lean data 2026-05-10T05:51:42+02:00")))}\\' + '\n')
            f.write(r'\hline\addlinespace[0.20em]' + '\n')
            compact_unprepared = (phase_status[phase] == 'W' and str(r.get('preparation_status', '')).strip() in {'not-prepared', ''})
            if compact_unprepared:
                compact_fields = [
                    ('Implementation status', r.get('implementation_status', '')),
                    ('Preparation status', r.get('preparation_status', '')),
                    ('Phase type', r.get('phase_type', '')),
                    ('Phase-type-specific contract', r.get('phase_type_specific_contract', '')),
                    ('Preparation workflow', r.get('preparation_workflow', '')),
                    ('Dependency-depth audit', r.get('dependency_depth_audit', '')),
                    ('Proof rehearsal before implementation', r.get('proof_rehearsal', '')),
                    ('Bridge gap status', r.get('bridge_gap_status', '')),
                ]
                for key, val in compact_fields:
                    if str(val).strip():
                        f.write(rf'{esc(key)} & {esc(val)}\\' + '\n')
                        f.write(r'\hline\addlinespace[0.20em]' + '\n')
                f.write(r'\end{longtable}' + '\n')
                continue
            plain_fields = [
                ('Implementation status', r.get('implementation_status', '')),
                ('Preparation status', r.get('preparation_status', '')),
                ('Phase type', r.get('phase_type', '')),
                ('Phase-type-specific contract', r.get('phase_type_specific_contract', '')),
                ('Title / state', r.get('title', '')),
                ('Preparation workflow', r.get('preparation_workflow', '')),
                ('Source-to-CNNA mapping', r.get('source_to_cnna_mapping', '')),
                ('Dependency-depth audit', r.get('dependency_depth_audit', '')),
                ('Phase split decision', r.get('phase_split_decision', '')),
                ('Positive path plan', r.get('positive_path_plan', '')),
                ('Module implementation manifest', r.get('module_implementation_manifest', '')),
                ('Semantic placement decision', r.get('semantic_placement_decision', '')),
                ('Reuse and duplication audit', r.get('reuse_and_duplication_audit', '')),
                ('Canonical generator policy', r.get('canonical_generator_policy', '')),
                ('Module compactness rule', r.get('module_compactness_rule', '')),
                ('Refactor regression protocol', r.get('refactor_regression_protocol', '')),
                ('Refactor migration metrics', r.get('refactor_migration_metrics', '')),
                ('Lean/mathlib version policy', r.get('lean_mathlib_version_policy', '')),
                ('ExecComplex boundary policy', r.get('exec_complex_boundary_policy', '')),
                ('Consumer-contract direction', r.get('consumer_contract_direction', '')),
                ('Governance-overhead review', r.get('governance_overhead_review', '')),
                ('Proof rehearsal before implementation', r.get('proof_rehearsal', '')),
                ('Expected tactics', r.get('expected_tactics', '')),
                ('Expected mathlib imports', r.get('expected_mathlib_imports', '')),
                ('ExecComplex/computable plan', r.get('exec_complex_plan', '')),
                ('Concrete computable instance traversal', r.get('concrete_instance_traversal', '')),
                ('Computable path non-skeleton status', r.get('computable_path_not_skeleton_status', '')),
                ('Expected executable witness', r.get('expected_executable_witness', '')),
                ('Mathlib complication log', r.get('mathlib_complication_log', '')),
                ('Noncomputable boundary audit', r.get('noncomputable_boundary_audit', '')),
                ('Mathlib mitigation/refactor layer', r.get('mathlib_mitigation_or_refactor_layer', '')),
                ('Bridge gap status', r.get('bridge_gap_status', '')),
                ('Natural backjump/refactor layer', r.get('natural_backjump_or_refactor_layer', '')),
                ('Implementation prompt contract', r.get('implementation_prompt_contract', '')),
                ('Global no-go inheritance', r.get('global_no_go_inheritance', '')),
                ('How implemented', r.get('how_implemented', '')),
                ('Verification / evidence', r.get('verification_evidence', '')),
                ('Proof strategy', r.get('proof_strategy', '')),
                ('Build result', r.get('build_result', '')),
                ('Post-implementation plan check', r.get('post_implementation_plan_check', '')),
                ('Artifact packaging rule', r.get('artifact_packaging_rule', '')),
                ('Implementation notes', r.get('implementation_notes', '')),
            ]
            for key, val in plain_fields:
                if str(val).strip():
                    f.write(rf'{esc(key)} & {esc(val)}\\' + '\n')
                    f.write(r'\hline\addlinespace[0.20em]' + '\n')
            list_fields = [
                ('Source materials / references', r.get('source_materials', [])),
                ('Extracted established theory objects', r.get('extracted_theory_objects', [])),
                ('Implemented modules', r.get('implemented_modules', [])),
                ('Added modules', r.get('added_modules', [])),
                ('Modified modules', r.get('modified_modules', [])),
                ('Forbidden patterns checked', r.get('forbidden_patterns_checked', [])),
                ('No-go guardrails', r.get('no_go_guardrails', [])),
                ('Proposed added modules', r.get('proposed_added_modules', [])),
                ('Proposed modified modules', r.get('proposed_modified_modules', [])),
                ('Reusable existing modules', r.get('reusable_existing_modules', [])),
                ('Duplicate-risk symbols or operations', r.get('duplicate_risk_symbols', [])),
            ]
            for key, items in list_fields:
                if items:
                    f.write(rf'{esc(key)} & {list_tex(items)}\\' + '\n')
                    f.write(r'\hline\addlinespace[0.20em]' + '\n')
            f.write(r'\end{longtable}' + '\n')
        f.write(r'\arrayrulecolor{black}' + '\n')
        f.write(r'\normalsize' + '\n')


def scratch_list_plain(items: Any) -> str:
    if not items:
        return ''
    if isinstance(items, list):
        return '; '.join(str(x) for x in items)
    return str(items)


def manifest_field_is_filled(v: Any) -> bool:
    if v is None or v == []:
        return False
    s = str(v).strip()
    return bool(s) and s not in {'[]', 'none', 'none yet', 'not specified yet'}


def write_module_implementation_manifest(scratch_rows: List[Dict[str, Any]], phase_rows: List[Dict[str, str]]) -> None:
    phase_status = {r['Phase']: r['Phase status'] for r in phase_rows}
    phase_title = {r['Phase']: r['Main goal'] for r in phase_rows}
    phase_context = {r['Phase']: r.get('Context class', '') for r in phase_rows}

    export_rows: List[Dict[str, str]] = []
    tex_rows: List[Dict[str, str]] = []
    for r in scratch_rows:
        ph = str(r.get('phase_id', '')).strip()
        base = {
            'Phase': ph,
            'Phase status': phase_status.get(ph, str(r.get('phase_status', ''))),
            'Phase type': str(r.get('phase_type', '')),
            'Context class': phase_context.get(ph, ''),
            'Title': phase_title.get(ph, str(r.get('title', ''))),
            'Added modules': scratch_list_plain(r.get('proposed_added_modules', [])),
            'Modified modules': scratch_list_plain(r.get('proposed_modified_modules', [])),
            'Reusable existing modules': scratch_list_plain(r.get('reusable_existing_modules', [])),
            'Manifest rule': str(r.get('module_implementation_manifest', '')),
            'Semantic placement': str(r.get('semantic_placement_decision', '')),
            'Reuse/duplication audit': str(r.get('reuse_and_duplication_audit', '')),
            'Canonical generator policy': str(r.get('canonical_generator_policy', '')),
            'Compactness rule': str(r.get('module_compactness_rule', '')),
            'Duplicate risks': scratch_list_plain(r.get('duplicate_risk_symbols', [])),
            'Consumer direction': str(r.get('consumer_contract_direction', '')),
            'Regression protocol': str(r.get('refactor_regression_protocol', '')),
            'Lean/mathlib policy': str(r.get('lean_mathlib_version_policy', '')),
            'Concrete traversal': str(r.get('concrete_instance_traversal', '')),
            'Mathlib complication log': str(r.get('mathlib_complication_log', '')),
            'Noncomputable boundary audit': str(r.get('noncomputable_boundary_audit', '')),
        }
        export_rows.append(base)
        meaningful = (
            base['Phase status'] in {'Y', 'R'}
            or any(manifest_field_is_filled(r.get(k, '')) for k in (
                'module_implementation_manifest', 'semantic_placement_decision',
                'reuse_and_duplication_audit', 'canonical_generator_policy',
                'module_compactness_rule', 'proposed_added_modules',
                'proposed_modified_modules', 'reusable_existing_modules',
                'duplicate_risk_symbols'
            ))
        )
        if meaningful:
            tex_rows.append({
                'Phase': phase_link_cell(ph),
                'Status': base['Phase status'],
                'Phase type': base['Phase type'],
                'Context class': context_class_cell(base['Context class']),
                'Added modules': list_tex(r.get('proposed_added_modules', [])),
                'Modified modules': list_tex(r.get('proposed_modified_modules', [])),
                'Reusable existing modules': list_tex(r.get('reusable_existing_modules', [])),
                'Manifest / placement / compactness': '; '.join(x for x in [
                    base['Manifest rule'], base['Semantic placement'], base['Compactness rule']
                ] if str(x).strip()),
                'Reuse / generator / duplicate risks': '; '.join(x for x in [
                    base['Reuse/duplication audit'], base['Canonical generator policy'], base['Duplicate risks']
                ] if str(x).strip()),
                'Implementation risk fields': '; '.join(x for x in [
                    base['Consumer direction'], base['Regression protocol'], base['Lean/mathlib policy'],
                    base['Concrete traversal'], base['Mathlib complication log'], base['Noncomputable boundary audit']
                ] if str(x).strip()),
            })

    write_export_tsv('module_implementation_manifest.generated.tsv', export_rows)
    longtable(
        ['Phase', 'Status', 'Phase type', 'Context class', 'Added modules', 'Modified modules', 'Reusable existing modules', 'Manifest / placement / compactness', 'Reuse / generator / duplicate risks', 'Implementation risk fields'],
        [0.026, 0.024, 0.045, 0.070, 0.065, 0.075, 0.110, 0.190, 0.155, 0.170],
        tex_rows,
        'module_implementation_manifest_table.tex',
        r'\footnotesize',
        {'Status'},
        {'Phase', 'Context class', 'Added modules', 'Modified modules', 'Reusable existing modules'},
        legend='phase'
    )
    (T / 'module_implementation_manifest.tex').write_text(r'''\paragraph{Module-change manifest rule.} This appendix is not a second phase table and does not release phases. It is a narrow technical ledger used only when a phase proposes new Lean modules, module moves, module merges, public API changes, import-surface changes, generator seams, or compatibility facades. Its rows are generated from implementation-scratchpad module/refactor fields; phases without module/API changes do not need meaningful rows here. The main phase table remains the primary status and release surface.
\input{tables/module_implementation_manifest_table.tex}
''', encoding='utf-8')


def tex_breakable_dotted_name(value: str) -> str:
    return esc(value).replace('.', r'.\allowbreak{}')


def module_source_link(module: str, path: str) -> str:
    target = 'repo_snapshot/' + str(path)
    return rf'\href{{run:{target}}}{{{tex_breakable_dotted_name(module)}}}'


def short_module_label(module: str) -> str:
    parts = str(module).split('.')
    if len(parts) <= 2:
        return str(module)
    return '.'.join(parts[-2:])


def write_dot_and_render(dot_text: str, dot_path: Path, pdf_path: Path) -> bool:
    dot_path.write_text(dot_text, encoding='utf-8')
    try:
        subprocess.run(['dot', '-Tpdf', str(dot_path), '-o', str(pdf_path)], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return True
    except Exception:
        return False



def read_json_if_present(path: Path) -> Dict[str, Any]:
    if not path.exists():
        return {}
    try:
        payload = json.loads(path.read_text(encoding='utf-8'))
        return payload if isinstance(payload, dict) else {}
    except Exception:
        return {}


def count_lean_source_files() -> Tuple[int, int, int]:
    files = sorted((ROOT / 'repo_snapshot').rglob('*.lean'))
    line_count = 0
    byte_count = 0
    for path in files:
        try:
            text = path.read_text(encoding='utf-8')
        except UnicodeDecodeError:
            text = path.read_text(encoding='utf-8', errors='ignore')
        line_count += text.count('\n') + (1 if text else 0)
        byte_count += path.stat().st_size
    return len(files), line_count, byte_count


def write_guiding_metaphors(rows: List[Dict[str, str]]) -> None:
    if not rows:
        (T / 'guiding_metaphors.tex').write_text('', encoding='utf-8')
        return
    required = {'ID', 'Name', 'Metaphor', 'Mapping', 'Operational consequence', 'Boundary'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('guiding_metaphors misses required columns: ' + ', '.join(sorted(missing)))
    ids = [r.get('ID', '') for r in rows]
    if len(ids) != len(set(ids)):
        fail('guiding_metaphors contains duplicate IDs')
    write_export_tsv('guiding_metaphors.generated.tsv', rows)
    longtable(['ID', 'Name', 'Metaphor', 'Mapping', 'Operational consequence', 'Boundary'],
              [0.055, 0.115, 0.195, 0.315, 0.190, 0.095], rows,
              'guiding_metaphors_table.tex', r'\footnotesize')
    (T / 'guiding_metaphors.tex').write_text(
        r'''\paragraph{Guiding-metaphor rule.} Guiding metaphors are operational documentation aids. They may help identify review boundaries, hidden dependencies, and interface duties, but they are not formal CNNA theorems, ontic inputs, or substitutes for Lean-primary proof and discipline-specific expert review.
\input{tables/guiding_metaphors_table.tex}
''',
        encoding='utf-8'
    )


def write_license_notice(rows: List[Dict[str, str]]) -> None:
    if not rows:
        (T / 'license_notice.tex').write_text('', encoding='utf-8')
        return
    required = {'Scope', 'License', 'Reference', 'Boundary'}
    missing = required.difference(rows[0].keys())
    if missing:
        fail('license_notice misses required columns: ' + ', '.join(sorted(missing)))
    write_export_tsv('license_notice.generated.tsv', rows)
    longtable(['Scope', 'License', 'Reference', 'Boundary'],
              [0.210, 0.185, 0.220, 0.350], rows,
              'license_notice_table.tex', r'\footnotesize')
    (T / 'license_notice.tex').write_text(
        r'''\paragraph{License notice.} Project-authored documentation, prose, generated reports, and PDFs are declared under CC BY 4.0; project-authored source code, Lean files, Python scripts, and tool code are declared under the MIT License. Third-party dependencies, upstream libraries, and quoted/reference material retain their own licenses and rights. Project credits: Editor -- Jan Seeck (antaris); Assistant -- ChatGPT (OpenAI).
\input{tables/license_notice_table.tex}
''',
        encoding='utf-8'
    )


def build_project_stats_rows(data: Dict[str, Any]) -> List[Dict[str, str]]:
    raw = ROOT / 'repo_inventory' / 'raw_export'
    stats = read_json_if_present(raw / 'stats.json')
    symbol = read_json_if_present(raw / 'symbol_reference_summary.json')
    core = read_json_if_present(raw / 'architectural_core_summary.json')
    lean_files, lean_lines, lean_bytes = count_lean_source_files()
    phases = normalize_rows(data.get('phases', []), 'phases')
    objects = normalize_rows(data.get('objects', []), 'objects')
    proof_dossiers = normalize_rows(data.get('object_proof_dossiers', []), 'object_proof_dossiers')
    scratch = data.get('implementation_scratchpad', []) or []
    context_profiles = data.get('context_documentation_profiles', []) or []
    rows = [
        {'Area': 'Tool infrastructure version', 'Metric': 'current tool code/generator version', 'Value': version_meta(data.get('metadata', {}), 'tool_infrastructure_version'), 'Source': 'metadata.tool_infrastructure_version', 'Review status': 'generated-secondary; changes only when tool code changes'},
        {'Area': 'Planning data version', 'Metric': 'current YAML planning/register version', 'Value': version_meta(data.get('metadata', {}), 'planning_data_version'), 'Source': 'metadata.planning_data_version', 'Review status': 'generated-secondary planning state; not Lean truth'},
        {'Area': 'Lean data', 'Metric': 'Lean toolchain version', 'Value': version_meta(data.get('metadata', {}), 'lean_data_version'), 'Source': 'metadata.lean_data_version', 'Review status': 'static Lean toolchain/API level; not source timestamp'},
        {'Area': 'Lean data', 'Metric': 'fixed Lean-code data timestamp', 'Value': version_meta(data.get('metadata', {}), 'lean_data_timestamp'), 'Source': 'metadata.lean_data_timestamp', 'Review status': 'Lean-primary timestamp only; not semantic infallibility'},
        {'Area': 'Credits', 'Metric': 'editor', 'Value': str(data.get('metadata', {}).get('editor', 'Jan Seeck (antaris)')), 'Source': 'metadata.editor', 'Review status': 'project credit metadata; generated-secondary'},
        {'Area': 'Credits', 'Metric': 'assistant', 'Value': str(data.get('metadata', {}).get('assistant', 'ChatGPT (OpenAI)')), 'Source': 'metadata.assistant', 'Review status': 'project credit metadata; generated-secondary'},
        {'Area': 'Assistant workflow', 'Metric': 'minimum tested setup', 'Value': str(data.get('metadata', {}).get('minimum_assistant_requirement', 'ChatGPT Plus account with GPT-5.5')), 'Source': 'metadata.minimum_assistant_requirement', 'Review status': 'tested ChatGPT-instantiated workflow assumption; not a CNNA input'},
        {'Area': 'Lean code extent', 'Metric': 'Lean source files', 'Value': str(lean_files), 'Source': 'repo_snapshot/**/*.lean', 'Review status': 'generated source-file count'},
        {'Area': 'Lean code extent', 'Metric': 'Lean source lines', 'Value': str(lean_lines), 'Source': 'repo_snapshot/**/*.lean', 'Review status': 'generated line count; comments/prose included'},
        {'Area': 'Lean code extent', 'Metric': 'Lean source size bytes', 'Value': str(lean_bytes), 'Source': 'repo_snapshot/**/*.lean', 'Review status': 'generated byte count'},
        {'Area': 'Module inventory', 'Metric': 'registered Lean modules', 'Value': str(stats.get('module_count', 'unknown')), 'Source': 'repo_inventory/raw_export/stats.json', 'Review status': 'generated module inventory'},
        {'Area': 'Module inventory', 'Metric': 'internal import edges', 'Value': str(stats.get('internal_edge_count', 'unknown')), 'Source': 'repo_inventory/raw_export/stats.json', 'Review status': 'generated import graph'},
        {'Area': 'Module inventory', 'Metric': 'missing internal import edges', 'Value': str(stats.get('missing_internal_edge_count', 'unknown')), 'Source': 'repo_inventory/raw_export/stats.json', 'Review status': 'should remain zero for inventory consistency'},
        {'Area': 'Module inventory', 'Metric': 'acyclic internal import graph', 'Value': str(stats.get('acyclic', 'unknown')), 'Source': 'repo_inventory/raw_export/stats.json', 'Review status': 'graph property; not semantic correctness'},
        {'Area': 'Symbol/reference inventory', 'Metric': 'declarations detected', 'Value': str(symbol.get('declaration_count', stats.get('symbol_references', {}).get('declaration_count', 'unknown'))), 'Source': 'symbol_reference_summary.json', 'Review status': 'static extraction; may miss semantic intent'},
        {'Area': 'Symbol/reference inventory', 'Metric': 'reference edges detected', 'Value': str(symbol.get('reference_edge_count', stats.get('symbol_references', {}).get('reference_edge_count', 'unknown'))), 'Source': 'symbol_reference_summary.json', 'Review status': 'static extraction; review required'},
        {'Area': 'Architectural core', 'Metric': 'core modules', 'Value': str(core.get('core_module_count', stats.get('architectural_core', {}).get('core_module_count', 'unknown'))), 'Source': 'architectural_core_summary.json', 'Review status': 'generated architectural classification'},
        {'Area': 'Architectural core', 'Metric': 'artifact modules', 'Value': str(core.get('artifact_module_count', stats.get('architectural_core', {}).get('artifact_module_count', 'unknown'))), 'Source': 'architectural_core_summary.json', 'Review status': 'generated architectural classification'},
        {'Area': 'Planning register', 'Metric': 'registered phases', 'Value': str(len(phases)), 'Source': 'masters/cnna_roadmap_master.yaml', 'Review status': 'YAML planning count'},
        {'Area': 'Planning register', 'Metric': 'registered objects/quantities', 'Value': str(len(objects)), 'Source': 'masters/cnna_roadmap_master.yaml', 'Review status': 'YAML planning count'},
        {'Area': 'Planning register', 'Metric': 'proof dossiers', 'Value': str(len(proof_dossiers)), 'Source': 'masters/cnna_roadmap_master.yaml', 'Review status': 'YAML planning count'},
        {'Area': 'Planning register', 'Metric': 'implementation scratchpad records', 'Value': str(len(scratch)), 'Source': 'masters/cnna_roadmap_master.yaml', 'Review status': 'YAML planning count'},
        {'Area': 'Review governance', 'Metric': 'global no-go guardrails', 'Value': str(len(data.get('global_no_go_guardrails', []) or [])), 'Source': 'masters/cnna_roadmap_master.yaml', 'Review status': 'governance count; not proof'},
        {'Area': 'Review governance', 'Metric': 'context documentation profiles', 'Value': str(len(context_profiles)), 'Source': 'masters/cnna_roadmap_master.yaml', 'Review status': 'profile count; false negatives remain possible'},
        {'Area': 'License', 'Metric': 'documentation/prose/generated reports', 'Value': 'CC BY 4.0', 'Source': 'license_notice', 'Review status': 'project-authored artifacts unless stated otherwise'},
        {'Area': 'License', 'Metric': 'source code/scripts/Lean files', 'Value': 'MIT', 'Source': 'license_notice', 'Review status': 'project-authored code unless stated otherwise'},
    ]
    return rows


def write_stats_section(data: Dict[str, Any]) -> None:
    rows = build_project_stats_rows(data)
    write_export_tsv('project_stats.generated.tsv', rows)
    longtable(['Area', 'Metric', 'Value', 'Source', 'Review status'],
              [0.130, 0.205, 0.100, 0.235, 0.285], rows,
              'project_stats_table.tex', r'\footnotesize')
    write_guiding_metaphors(normalize_rows(data.get('guiding_metaphors', []), 'guiding_metaphors'))
    write_license_notice(normalize_rows(data.get('license_notice', []), 'license_notice'))
    (T / 'stats.tex').write_text(
        r'''\paragraph{Stats rule.} This opening section is a generated-secondary orientation surface. It summarizes project scale, credits, license status, root/source layout and review context, then embeds the repository module inventory and derivation graphs. None of these counts, graphs, notices, or metaphors replaces the Lean code as primary formal source, and none removes the need for discipline-specific expert review.
\subsection*{Project facts}
\input{tables/project_stats_table.tex}
\subsection*{Tool-interface guiding metaphor}
\input{tables/guiding_metaphors.tex}
\subsection*{License notice}
\input{tables/license_notice.tex}
\subsection*{Repository module inventory and derivation graphs}
\input{tables/module_inventory.tex}
''',
        encoding='utf-8'
    )

def write_repo_inventory_tables() -> None:
    raw = ROOT / 'repo_inventory' / 'raw_export'
    if not raw.exists():
        (T / 'module_inventory.tex').write_text('No generated Lean module inventory found.\\n', encoding='utf-8')
        return
    modules_json = raw / 'modules.json'
    stats_json = raw / 'stats.json'
    if not modules_json.exists() or not stats_json.exists():
        (T / 'module_inventory.tex').write_text('Generated Lean module inventory is incomplete.\\n', encoding='utf-8')
        return
    modules_payload = json.loads(modules_json.read_text(encoding='utf-8'))
    stats = json.loads(stats_json.read_text(encoding='utf-8'))
    modules = modules_payload.get('modules', [])
    by_mod = {m['module']: m for m in modules}
    dependency_order = stats.get('dependency_order', [m['module'] for m in modules])

    symbol_summary = {}
    symbol_path = raw / 'symbol_reference_summary.json'
    if symbol_path.exists():
        symbol_summary = json.loads(symbol_path.read_text(encoding='utf-8'))
    core_summary = {}
    core_path = raw / 'architectural_core_summary.json'
    if core_path.exists():
        core_summary = json.loads(core_path.read_text(encoding='utf-8'))
    summary_rows = [
        {'Metric': 'Lean modules', 'Value': str(stats.get('module_count', len(modules)))},
        {'Metric': 'Internal import edges', 'Value': str(stats.get('internal_edge_count', ''))},
        {'Metric': 'External import edges', 'Value': str(stats.get('external_edge_count', ''))},
        {'Metric': 'Missing internal imports', 'Value': str(stats.get('missing_internal_edge_count', ''))},
        {'Metric': 'Import graph acyclic', 'Value': str(stats.get('acyclic', ''))},
        {'Metric': 'Symbol declarations detected', 'Value': str(symbol_summary.get('declaration_count', ''))},
        {'Metric': 'Symbol-reference edges detected', 'Value': str(symbol_summary.get('reference_edge_count', ''))},
        {'Metric': 'Architectural core modules', 'Value': str(core_summary.get('core_module_count', ''))},
        {'Metric': 'Artifact/build/notation/top-level modules', 'Value': str(core_summary.get('artifact_module_count', ''))},
    ]
    longtable(['Metric', 'Value'], [0.26, 0.70], summary_rows, 'module_inventory_summary.tex', r'\small')

    cat_rows=[]
    for i, mod in enumerate(dependency_order, start=1):
        m=by_mod.get(mod)
        if not m:
            continue
        flags=[]
        if m.get('is_build_module'):
            flags.append('BuildAll')
        if m.get('is_notation_module'):
            flags.append('Notation')
        if m.get('prelude'):
            flags.append('prelude')
        path = m.get('path','')
        cat_rows.append({
            '#': str(i),
            'Module': module_source_link(mod, path),
            'Group': str(m.get('group','')),
            'Path': rf'\href{{run:repo_snapshot/{path}}}{{{tex_breakable_dotted_name(path)}}}',
            'Imports': str(len(m.get('internal_imports', []))),
            'Imported by': str(len(m.get('internal_imported_by', []))),
            'Flags': ', '.join(flags) if flags else '---',
        })
    longtable(['#', 'Module', 'Group', 'Path', 'Imports', 'Imported by', 'Flags'],
              [0.025, 0.315, 0.080, 0.315, 0.045, 0.055, 0.070], cat_rows, 'module_catalog.tex', r'\footnotesize', raw_cols={'Module','Path'})

    group_rows=[]
    gp=raw/'group_summary.json'
    groups={}
    if gp.exists():
        groups=json.loads(gp.read_text(encoding='utf-8')).get('groups', {})
        for gname,g in sorted(groups.items(), key=lambda kv: kv[0]):
            group_rows.append({
                'Group': gname,
                'Modules': str(g.get('module_count','')),
                'Internal edges': str(g.get('internal_edge_count','')),
                'Outgoing edges': str(g.get('outgoing_edge_count','')),
                'Incoming edges': str(g.get('incoming_edge_count','')),
            })
    if group_rows:
        longtable(['Group','Modules','Internal edges','Outgoing edges','Incoming edges'], [0.36,0.10,0.14,0.14,0.14], group_rows, 'module_group_summary.tex', r'\small')

    hotspot_rows=[]
    hp=raw/'hotspots.json'
    if hp.exists():
        hot=json.loads(hp.read_text(encoding='utf-8')).get('top_internal_out_degree', [])[:20]
        for h in hot:
            mod=h.get('module','')
            hotspot_rows.append({
                'Module': module_source_link(mod, by_mod.get(mod,{}).get('path','')),
                'Group': str(h.get('group','')),
                'Imports': str(h.get('internal_out_degree','')),
                'Imported by': str(h.get('internal_in_degree','')),
                'Transitive imports': str(h.get('transitive_internal_imports','')),
                'Flags': ', '.join(x for x in [('BuildAll' if h.get('is_build_module') else ''), ('Notation' if h.get('is_notation_module') else '')] if x),
            })
    if hotspot_rows:
        longtable(['Module','Group','Imports','Imported by','Transitive imports','Flags'], [0.42,0.16,0.07,0.08,0.10,0.09], hotspot_rows, 'module_hotspots.tex', r'\footnotesize', raw_cols={'Module'})

    figdir = ROOT / 'figures'
    figdir.mkdir(exist_ok=True)
    if groups:
        group_dot=[]
        group_dot.append('digraph G {')
        group_dot.append('  graph [rankdir=LR, bgcolor="white", margin=0.05];')
        group_dot.append('  node [shape=box, style="rounded,filled", fillcolor="white", fontname="DejaVu Sans", fontsize=11];')
        group_dot.append('  edge [color="gray35", arrowsize=0.6];')
        edge_set=set()
        for gname,g in groups.items():
            label=f'{gname}\\n({g.get("module_count",0)} modules)'
            group_dot.append(f'  "{gname}" [label="{label}"];')
            for e in g.get('outgoing_edges',[]):
                s=e.get('source_group', gname); t=e.get('target_group')
                if s and t and s!=t:
                    edge_set.add((s,t))
        for s0,t0 in sorted(edge_set):
            group_dot.append(f'  "{s0}" -> "{t0}";')
        group_dot.append('}')
        write_dot_and_render('\n'.join(group_dot), figdir/'module_group_dependency_graph.dot', figdir/'module_group_dependency_graph.pdf')

    # A readable staged derivation view of the robust semantic mainline.
    # The full node-level mainline remains available in repo_inventory/raw_export.
    stages = [
        ('generated source\nmain path', 'GeneratedMainPath / GeneratedApproximantCore'),
        ('boundary and\npartition', 'BoundaryInteriorPartition / DirichletEntry'),
        ('interior block and\nelimination candidate', 'InteriorBlock / CandidateEntry'),
        ('trace, fold and\naccumulated entry', 'TraceEvaluation / AccumulatedEntryFold'),
        ('local cancellation\nand pivot scale', 'LocalStepCancellation / PivotScaleWitness'),
        ('terminal identity\nand two-sided inverse', 'TerminalIdentity / ProductIdentity / TwoSidedInv'),
        ('DtN and generalized\nboundary operator', 'GeneratedDtN / GeneralizedDtN / MultiSchur'),
        ('Exec boundary\nand arithmetic source', 'ExecBoundaryOperator / ArithmeticSource'),
        ('level history\nExec matrix', 'LevelHistory / ExecMatrix / Mirror'),
        ('charpoly, recurrence\nand window', 'CharpolyExec / CoeffRecurrence / QuadraticWindow'),
        ('operational\ndiscriminant', 'OperationalQuadraticDiscriminantSourceSM9h'),
    ]
    dot=['digraph G {', '  graph [rankdir=LR, bgcolor="white", margin=0.05, nodesep=0.45, ranksep=0.55];', '  node [shape=box, style="rounded,filled", fillcolor="white", fontname="DejaVu Sans", fontsize=11];', '  edge [color="gray30", arrowsize=0.7];']
    for idx,(title,detail) in enumerate(stages):
        label=f'{idx+1}. {title}\n{detail}'
        dot.append(f'  s{idx} [label="{label}"];')
    for idx in range(len(stages)-1):
        dot.append(f'  s{idx} -> s{idx+1};')
    dot.append('}')
    write_dot_and_render('\n'.join(dot), figdir/'core_robust_semantic_mainline.dot', figdir/'core_robust_semantic_mainline.pdf')

    graph_lines=[]
    if (ROOT/'figures/module_group_dependency_graph.pdf').exists():
        graph_lines.append('\\subsection*{Graph A: group-level import/dependency overview}')
        graph_lines.append('\\paragraph{Arrow convention.} An edge \\(A \\to B\\) means that at least one module in group \\(A\\) imports or depends on a module in group \\(B\\). The arrow points from the importing/consuming group to the required dependency. This is a technical import graph, not a semantic derivation graph.')
        graph_lines.append('\\begin{center}\\includegraphics[width=0.98\\linewidth,height=0.40\\textheight,keepaspectratio]{figures/module_group_dependency_graph.pdf}\\end{center}')
    if (ROOT/'figures/core_robust_semantic_mainline.pdf').exists():
        graph_lines.append('\\subsection*{Graph B: robust semantic core mainline}')
        graph_lines.append('\\paragraph{Arrow convention.} An edge \\(A \\to B\\) means that \\(B\\) is the next curated semantic construction step derived from \\(A\\) along the robust core mainline. The arrow points in the intended derived-only construction direction. This is a semantic mainline view, not a complete import graph.')
        graph_lines.append('\\begin{center}\\includegraphics[width=0.98\\linewidth,height=0.32\\textheight,keepaspectratio]{figures/core_robust_semantic_mainline.pdf}\\end{center}')
    section = r'''
\paragraph{Module inventory rule.} This section is a generated repository view, not a second planning source. It is derived from the frozen SM9h Lean source snapshot by \texttt{scripts/build\_export\_script\_v1.8.py}. The planning YAML remains the only manually maintained roadmap source; the module catalog, dependency summaries, source-path links, and graph figures are regenerated from the repository snapshot.
\subsection*{Inventory summary}
\input{tables/module_inventory_summary.tex}
\subsection*{Module dependency graphs}
'''
    section += '\n'.join(graph_lines) + '\n'
    section += r'''
\subsection*{Group summary}
\input{tables/module_group_summary.tex}
\subsection*{Import hotspots}
\input{tables/module_hotspots.tex}
\subsection*{Complete Lean module catalog, dependency-first order}
\input{tables/module_catalog.tex}
'''
    (T/'module_inventory.tex').write_text(section, encoding='utf-8')

def main() -> None:
    data = load_master()
    # clear generated table tex files to avoid stale outputs
    for p in T.glob('*.tex'):
        p.unlink()
    phase_rows = normalize_rows(data['phases'], 'phases')
    object_rows = normalize_rows(data['objects'], 'objects')
    object_proof_rows = normalize_rows(data['object_proof_dossiers'], 'object_proof_dossiers')
    scratch_rows = data['implementation_scratchpad']
    if not isinstance(scratch_rows, list):
        fail('implementation_scratchpad must be a list of records')
    # Keep original list-valued scratchpad fields while normalizing scalar keys enough for validators.
    scratch_for_validation = [{k: (str(v) if not isinstance(v, list) else v) for k, v in rec.items()} for rec in scratch_rows]

    scratch_by_phase = validate_inputs(phase_rows, scratch_for_validation)
    validate_object_register(object_rows, phase_rows)
    validate_object_proof_dossiers(object_proof_rows, object_rows)

    # optional generated TSV snapshots; not authoritative
    write_export_tsv('phase_roadmap.generated.tsv', phase_rows)
    write_export_tsv('object_register.generated.tsv', object_rows)
    write_export_tsv('object_proof_documentation.generated.tsv', object_proof_rows)
    for sec in ['status_legend', 'access_policy', 'code_audit', 'format_decision', 'workflow_policy', 'pre_implementation_phase_check_policy', 'pre_implementation_phase_check_results', 'implementation_scaling_phase_plan', 'global_no_go_guardrails', 'global_postulates', 'phase_object_link_policy', 'context_class_taxonomy', 'object_significance_taxonomy', 'lean_declaration_classification_taxonomy', 'reuse_duplication_ledger', 'consumption_classification_map', 'guiding_metaphors', 'license_notice']:
        write_export_tsv(f'{sec}.generated.tsv', normalize_rows(data[sec], sec))
    if 'secondary_long_term_goals' in data:
        write_export_tsv('secondary_long_term_goals.generated.tsv', normalize_rows(data['secondary_long_term_goals'], 'secondary_long_term_goals'))
    if 'external_source_crosscheck' in data:
        write_export_tsv('external_source_crosscheck.generated.tsv', normalize_rows(data['external_source_crosscheck'], 'external_source_crosscheck'))

    write_latest_change_overview(data['metadata'], normalize_rows(data['latest_change_overview'], 'latest_change_overview'))
    write_status_explanation_tables(data['status_legend'])
    # Standalone status/access tables are intentionally omitted from the PDF body; status explanations live at the start of the object and phase sections.
    write_code_audit(normalize_rows(data['code_audit'], 'code_audit'))
    longtable(['Topic', 'Assessment', 'Decision'], [0.18, 0.38, 0.40], normalize_rows(data['format_decision'], 'format_decision'), 'format_decision.tex', r'\small')
    write_workflow_policy(normalize_rows(data['workflow_policy'], 'workflow_policy'))
    write_pre_implementation_phase_check_policy(normalize_rows(data['pre_implementation_phase_check_policy'], 'pre_implementation_phase_check_policy'))
    write_pre_implementation_phase_check_results(normalize_rows(data['pre_implementation_phase_check_results'], 'pre_implementation_phase_check_results'), phase_rows)
    write_implementation_scaling_phase_plan(normalize_rows(data['implementation_scaling_phase_plan'], 'implementation_scaling_phase_plan'))
    write_global_no_go_guardrails(normalize_rows(data['global_no_go_guardrails'], 'global_no_go_guardrails'))
    write_global_postulates(normalize_rows(data['global_postulates'], 'global_postulates'))
    write_phase_object_link_policy(normalize_rows(data['phase_object_link_policy'], 'phase_object_link_policy'))
    write_context_class_taxonomy(normalize_rows(data['context_class_taxonomy'], 'context_class_taxonomy'))
    write_object_significance_taxonomy(normalize_rows(data['object_significance_taxonomy'], 'object_significance_taxonomy'))
    write_lean_declaration_classification_taxonomy(normalize_rows(data['lean_declaration_classification_taxonomy'], 'lean_declaration_classification_taxonomy'))
    write_reuse_duplication_ledger(normalize_rows(data['reuse_duplication_ledger'], 'reuse_duplication_ledger'))
    write_consumption_classification_map(normalize_rows(data['consumption_classification_map'], 'consumption_classification_map'), object_rows, object_proof_rows)
    if 'secondary_long_term_goals' in data:
        write_secondary_long_term_goals(normalize_rows(data['secondary_long_term_goals'], 'secondary_long_term_goals'))
    if 'external_source_crosscheck' in data:
        write_external_source_crosscheck(normalize_rows(data['external_source_crosscheck'], 'external_source_crosscheck'))
    write_repo_inventory_tables()
    write_stats_section(data)

    write_object_tables(object_rows)
    write_object_proof_documentation(object_proof_rows, object_rows)

    object_by_phase = phase_object_map(object_rows, phase_rows)
    ph = []
    for r in phase_rows:
        phase = r['Phase']
        ph.append({
            'Phase': phase_table_phase_cell(phase),
            'Status': r['Phase status'],
            'Context class': context_class_cell(r.get('Context class', '')),
            'Phase documentation tier': esc(r.get('Phase documentation tier', '')),
            'Doc tier': esc(r.get('Phase documentation tier', '')),
            'Linked objects': object_link_policy_cell(
                phase,
                object_by_phase.get(phase, []),
                r.get('Object link policy', ''),
                r.get('Object link explanation', ''),
                r.get('Child object scope', '')
            ),
            'Main goal': r['Main goal'],
            'Source objects/dependencies': r['Source objects/dependencies'],
            'Definitions/objects': r['Definitions/objects'],
            'Current code modules': r['Current code modules'],
            'Target modules/objects': r['Target modules/objects'],
            'Proof goals': r['Proof goals'],
            'How implemented': phase_record_link(phase, r['Phase status'], scratch_by_phase),
        })
    longtable(['Phase', 'Status', 'Context class', 'Doc tier', 'Linked objects', 'Main goal', 'Source objects/dependencies', 'Definitions/objects', 'Current code modules', 'Target modules/objects', 'Proof goals', 'How implemented'],
              [0.020, 0.022, 0.055, 0.042, 0.062, 0.076, 0.086, 0.088, 0.132, 0.095, 0.112, 0.050], ph, 'phase_table_single.tex', r'\footnotesize', {'Status'}, {'Phase', 'Linked objects', 'How implemented', 'Context class'}, legend='phase')
    (T / 'phase_table.tex').write_text(r"""\paragraph{Phase table rule.} This is the primary roadmap and release table. Green means closed/derived-only or governance-closed. Yellow is the unique active implementable phase. Orange means implementable only after the stated predecessor closure. Red is the default for unreleased Lean-derivation phases until they cite sufficient derived-only object/proof evidence. White is reserved for non-direct-Lean tooling, infrastructure, documentation, comparison, packaging, or refactor work. Context class is the orthogonal type/class field; Phase documentation tier is the orthogonal documentation-depth field: it distinguishes LeanDerivationPhase/LeanRefactorPhase from ToolInfrastructurePhase, DatabaseMirrorPhase, ReferenceGatePhase and generated/documentation classes. The module-change appendix must never replace this release logic.
\subsection*{Single phase table: derivation order, dependencies, code sites, proof goals, and implementation links}
\input{tables/phase_table_single.tex}
""", encoding='utf-8')


    write_module_implementation_manifest(scratch_rows, phase_rows)
    write_scratchpad(scratch_rows, phase_rows)
    print(f'Generated tables from one YAML master: {len(phase_rows)} phases, {len(object_rows)} objects, {len(scratch_rows)} scratch-pad records, {len(object_proof_rows)} proof-dossier records.')
    print(f'Authoritative source: {MASTER_FILE.relative_to(ROOT)}')


if __name__ == '__main__':
    main()
