#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from collections import Counter, defaultdict, deque
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Pattern


_IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*$")
_PRELUDE_RE = re.compile(r"^\s*prelude\s*$")
_NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$")
_SECTION_RE = re.compile(r"^\s*(?:private\s+)?section(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")
_END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")
_OPEN_RE = re.compile(r"^\s*open\s+(?!scoped\b)(.+?)\s*$")
_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|coinductive|axiom|opaque)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
)
_IDENT_TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
_SIGNATURE_SURFACE_RE = re.compile(
    r"^\s*(?:@[\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|coinductive|axiom|opaque|example)"
)
_STRUCTURE_HEAD_RE = re.compile(
    r"^\s*(?:@[\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*(?:structure|class)"
)
_FIELD_LINE_RE = re.compile(r"^\s{2,}([A-Za-z_][A-Za-z0-9_']*)\s*:")


def module_parent_namespace(module: str) -> str:
    return module.rsplit('.', 1)[0] if '.' in module else ''


def count_signature_surface_hits(text: str, token: str) -> int:
    if not token.strip():
        return 0
    hits = 0
    pattern = re.compile(rf"(?<![A-Za-z0-9_']){re.escape(token)}(?![A-Za-z0-9_'])")
    for line in text.splitlines():
        if token not in line:
            continue
        if not pattern.search(line):
            continue
        stripped = line.strip()
        if not stripped:
            continue
        if _SIGNATURE_SURFACE_RE.match(line) or ':' in line:
            hits += 1
    return hits


def extract_structure_field_names(text: str) -> list[str]:
    fields: list[str] = []
    seen: set[str] = set()
    in_structure = False
    for line in text.splitlines():
        if _STRUCTURE_HEAD_RE.match(line):
            in_structure = True
            continue
        stripped = line.strip()
        if in_structure:
            if not stripped:
                continue
            if not line.startswith(' ') and not line.startswith('	'):
                in_structure = False
                if _STRUCTURE_HEAD_RE.match(line):
                    in_structure = True
                continue
            m = _FIELD_LINE_RE.match(line)
            if m:
                name = m.group(1)
                if name not in seen:
                    seen.add(name)
                    fields.append(name)
    return fields


_CONFIDENCE_WEIGHTS: dict[str, int] = {
    "exact_qualified": 4,
    "qualified_suffix": 3,
    "same_namespace_short_name": 3,
    "anchored_open_namespace": 3,
    "open_namespace_alias": 2,
    "imported_unique_alias": 1,
}


@dataclass
class ModuleRecord:
    module: str
    path: str
    imports: list[str]
    internal_imports: list[str]
    external_imports: list[str]
    missing_internal_imports: list[str]
    imported_by: list[str]
    internal_imported_by: list[str]
    external_imported_by: list[str]
    transitive_internal_imports: list[str]
    prelude: bool
    is_build_module: bool
    is_notation_module: bool
    group: str
    path_after_source_root: list[str]


@dataclass
class DisciplineSpec:
    name: str
    description: str
    include_modules: list[str]
    include_prefixes: list[str]
    include_regexes: list[str]
    exclude_modules: list[str]
    exclude_prefixes: list[str]
    exclude_regexes: list[str]


@dataclass
class DisciplineCompiled:
    spec: DisciplineSpec
    include_patterns: list[Pattern[str]]
    exclude_patterns: list[Pattern[str]]


class ExportError(RuntimeError):
    pass


def strip_lean_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                i += 2
                continue
            if ch == "\n":
                out.append("\n")
            i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            i += 2
            continue
        if ch == "-" and nxt == "-":
            i += 2
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def parse_imports(path: Path) -> tuple[bool, list[str]]:
    raw = path.read_text(encoding="utf-8")
    text = strip_lean_comments(raw)
    imports: list[str] = []
    saw_prelude = False
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if _PRELUDE_RE.match(stripped):
            saw_prelude = True
            continue
        m = _IMPORT_RE.match(line)
        if m:
            imports.extend(token for token in m.group(1).split() if token)
            continue
        break
    return saw_prelude, sorted(set(imports))


def split_header_and_body(text: str) -> tuple[str, str]:
    header: list[str] = []
    body: list[str] = []
    in_header = True
    for line in text.splitlines():
        stripped = line.strip()
        if in_header and (not stripped or _PRELUDE_RE.match(stripped) or _IMPORT_RE.match(line)):
            header.append(line)
            continue
        in_header = False
        body.append(line)
    return "\n".join(header), "\n".join(body)


def strip_lean_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    in_string = False
    while i < n:
        ch = text[i]
        if in_string:
            if ch == "\\" and i + 1 < n:
                out.append(" ")
                out.append(" " if text[i + 1] != "\n" else "\n")
                i += 2
                continue
            if ch == '"':
                out.append(" ")
                in_string = False
                i += 1
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if ch == '"':
            out.append(" ")
            in_string = True
            i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def current_namespace_name(scope_stack: list[dict[str, str | None]]) -> str | None:
    for entry in reversed(scope_stack):
        if entry.get("kind") == "namespace":
            return entry.get("name")
    return None


def resolve_scoped_name(name: str, current_namespace: str | None) -> str:
    if name.startswith("_root_."):
        return name[len("_root_."):]
    if not current_namespace:
        return name
    if name.startswith(current_namespace + "."):
        return name
    current_root = current_namespace.split(".")[0]
    first_segment = name.split(".")[0]
    if "." in name and first_segment == current_root:
        return name
    return f"{current_namespace}.{name}"


def extract_module_declarations(module: str, body_text: str) -> list[dict[str, object]]:
    declarations: list[dict[str, object]] = []
    scope_stack: list[dict[str, str | None]] = []
    anon_section_counter = 0
    for lineno, line in enumerate(body_text.splitlines(), start=1):
        stripped = line.strip()
        if not stripped:
            continue
        m = _NAMESPACE_RE.match(stripped)
        if m:
            raw_name = m.group(1)
            scope_stack.append({
                "kind": "namespace",
                "raw": raw_name,
                "name": resolve_scoped_name(raw_name, current_namespace_name(scope_stack)),
            })
            continue
        m = _SECTION_RE.match(stripped)
        if m:
            anon_section_counter += 1
            raw_name = m.group(1) or f"__anon_section_{anon_section_counter}"
            scope_stack.append({"kind": "section", "raw": raw_name, "name": raw_name})
            continue
        m = _END_RE.match(stripped)
        if m:
            end_name = m.group(1)
            if not scope_stack:
                continue
            if end_name is None:
                scope_stack.pop()
                continue
            while scope_stack:
                entry = scope_stack.pop()
                candidates = {entry.get("raw"), entry.get("name")}
                full_name = entry.get("name")
                if isinstance(full_name, str):
                    candidates.add(full_name.split(".")[-1])
                if end_name in candidates:
                    break
            continue
        m = _DECL_RE.match(line)
        if m:
            raw_name = m.group(1)
            if raw_name.startswith("`") or raw_name.startswith("«"):
                continue
            current_namespace = current_namespace_name(scope_stack)
            full_name = resolve_scoped_name(raw_name, current_namespace)
            declarations.append({
                "module": module,
                "line": lineno,
                "raw_name": raw_name,
                "full_name": full_name,
                "basename": raw_name.split(".")[-1],
                "namespace": current_namespace,
            })
    return declarations


def extract_module_open_namespaces(module: str, body_text: str) -> list[str]:
    opened: set[str] = set()
    scope_stack: list[dict[str, str | None]] = []
    anon_section_counter = 0
    for line in body_text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        m = _NAMESPACE_RE.match(stripped)
        if m:
            raw_name = m.group(1)
            scope_stack.append({
                "kind": "namespace",
                "raw": raw_name,
                "name": resolve_scoped_name(raw_name, current_namespace_name(scope_stack)),
            })
            continue
        m = _SECTION_RE.match(stripped)
        if m:
            anon_section_counter += 1
            raw_name = m.group(1) or f"__anon_section_{anon_section_counter}"
            scope_stack.append({"kind": "section", "raw": raw_name, "name": raw_name})
            continue
        m = _END_RE.match(stripped)
        if m:
            end_name = m.group(1)
            if not scope_stack:
                continue
            if end_name is None:
                scope_stack.pop()
                continue
            while scope_stack:
                entry = scope_stack.pop()
                candidates = {entry.get("raw"), entry.get("name")}
                full_name = entry.get("name")
                if isinstance(full_name, str):
                    candidates.add(full_name.split(".")[-1])
                if end_name in candidates:
                    break
            continue
        m = _OPEN_RE.match(stripped)
        if not m:
            continue
        payload = re.split(r"\b(?:hiding|renaming|in)\b|\(", m.group(1), maxsplit=1)[0].strip()
        if not payload:
            continue
        current_namespace = current_namespace_name(scope_stack)
        for ident in _IDENT_TOKEN_RE.findall(payload):
            if ident in {"scoped", "hiding", "renaming", "in"}:
                continue
            opened.add(resolve_scoped_name(ident, current_namespace))
    return sorted(opened)


def build_unique_alias_map_for_declarations(decls: list[dict[str, object]]) -> dict[str, dict[str, object]]:
    alias_candidates: dict[str, list[dict[str, object]]] = defaultdict(list)
    for decl in decls:
        full_name = str(decl["full_name"])
        basename = str(decl["basename"])
        module = str(decl["module"])
        name_parts = full_name.split(".")
        prefix_parts = name_parts[:-1]
        module_parts = module.split(".")
        alias_candidates[basename].append(decl)
        for depth in range(1, min(4, len(prefix_parts) + 1)):
            alias = ".".join(prefix_parts[-depth:] + [basename])
            alias_candidates[alias].append(decl)
        for depth in range(1, min(4, len(module_parts) + 1)):
            alias = ".".join(module_parts[-depth:] + [basename])
            alias_candidates[alias].append(decl)
    unique_map: dict[str, dict[str, object]] = {}
    for alias, alias_decls in alias_candidates.items():
        unique = {str(d["full_name"]): d for d in alias_decls}
        if len(unique) == 1:
            unique_map[alias] = next(iter(unique.values()))
    return unique_map


def build_symbol_alias_maps(declarations_by_module: dict[str, list[dict[str, object]]]) -> tuple[dict[str, dict[str, object]], dict[str, dict[str, object]]]:
    all_decls = [decl for decls in declarations_by_module.values() for decl in decls]
    exact_map = {str(decl["full_name"]): decl for decl in all_decls}
    suffix_map = {
        alias: decl
        for alias, decl in build_unique_alias_map_for_declarations(all_decls).items()
        if alias not in exact_map
    }
    return exact_map, suffix_map



def compute_symbol_reference_export(
    records: list[ModuleRecord],
    module_to_path: dict[str, Path],
    dependency_adj: dict[str, list[str]],
    output_dir: Path,
) -> dict[str, object]:
    body_by_module: dict[str, str] = {}
    raw_text_by_module: dict[str, str] = {}
    declarations_by_module: dict[str, list[dict[str, object]]] = {}
    field_names_by_module: dict[str, list[str]] = {}
    open_namespaces_by_module: dict[str, list[str]] = {}
    local_declared_names_by_module: dict[str, set[str]] = {}
    imported_alias_maps: dict[str, dict[str, dict[str, object]]] = {}
    opened_alias_maps: dict[str, dict[str, dict[str, object]]] = {}
    opened_imported_decl_counts: dict[str, int] = {}

    for module, path in sorted(module_to_path.items()):
        raw_text = path.read_text(encoding="utf-8")
        raw_text_by_module[module] = raw_text
        stripped = strip_lean_comments(raw_text)
        _, body = split_header_and_body(stripped)
        body_by_module[module] = strip_lean_strings(body)
        declarations = extract_module_declarations(module, body)
        declarations_by_module[module] = declarations
        field_names_by_module[module] = extract_structure_field_names(body)
        open_namespaces = extract_module_open_namespaces(module, body)
        open_namespaces_by_module[module] = open_namespaces
        local_declared_names_by_module[module] = {
            str(decl["basename"]) for decl in declarations
        } | {
            str(decl["raw_name"]) for decl in declarations
        } | {
            str(decl["full_name"]) for decl in declarations
        }

    exact_map, suffix_map = build_symbol_alias_maps(declarations_by_module)
    module_declaration_counts = {module: len(decls) for module, decls in declarations_by_module.items()}

    for consumer in sorted(module_to_path):
        imported_modules = sorted(set(dependency_adj.get(consumer, [])))
        imported_decls = [
            decl
            for dependency in imported_modules
            for decl in declarations_by_module.get(dependency, [])
        ]
        imported_alias_maps[consumer] = build_unique_alias_map_for_declarations(imported_decls)
        opened_namespaces = open_namespaces_by_module.get(consumer, [])
        if opened_namespaces:
            opened_imported_decls = [
                decl
                for decl in imported_decls
                if any(
                    str(decl["full_name"]) == namespace
                    or str(decl["full_name"]).startswith(namespace + ".")
                    or (decl.get("namespace") is not None and (str(decl["namespace"]) == namespace or str(decl["namespace"]).startswith(namespace + ".")))
                    for namespace in opened_namespaces
                )
            ]
        else:
            opened_imported_decls = []
        opened_imported_decl_counts[consumer] = len(opened_imported_decls)
        opened_alias_maps[consumer] = build_unique_alias_map_for_declarations(opened_imported_decls)

    module_usage: dict[str, dict[str, object]] = {}
    aggregated_edges: list[dict[str, object]] = []
    semantic_dependency_adj: dict[str, list[str]] = {module: [] for module in module_to_path}
    confidence_totals: Counter[str] = Counter()
    referenced_symbol_names: set[str] = set()

    for consumer in sorted(module_to_path):
        imported_modules = set(dependency_adj.get(consumer, []))
        token_counts = Counter(_IDENT_TOKEN_RE.findall(body_by_module[consumer]))
        dep_hits: dict[str, dict[str, object]] = {}
        local_declared_names = local_declared_names_by_module.get(consumer, set())
        imported_alias_map = imported_alias_maps.get(consumer, {})
        opened_alias_map = opened_alias_maps.get(consumer, {})
        consumer_parent_namespace = module_parent_namespace(consumer)
        raw_consumer_text = raw_text_by_module[consumer]
        signature_surface_cache: dict[str, int] = {}

        for token, count in token_counts.items():
            if token in local_declared_names:
                continue
            decl = None
            confidence = None
            if token not in signature_surface_cache:
                signature_surface_cache[token] = count_signature_surface_hits(raw_consumer_text, token)
            token_signature_hits = signature_surface_cache[token]

            direct_decl = exact_map.get(token)
            if direct_decl is not None and str(direct_decl["module"]) in imported_modules:
                decl = direct_decl
                confidence = "exact_qualified"
            elif token in suffix_map and str(suffix_map[token]["module"]) in imported_modules:
                decl = suffix_map[token]
                confidence = "qualified_suffix"
            elif token in opened_alias_map and str(opened_alias_map[token]["module"]) in imported_modules:
                decl = opened_alias_map[token]
                if token_signature_hits >= 1 and token == str(decl["basename"]):
                    confidence = "anchored_open_namespace"
                else:
                    confidence = "open_namespace_alias"
            elif token in imported_alias_map and str(imported_alias_map[token]["module"]) in imported_modules:
                decl = imported_alias_map[token]
                dependency_module = str(decl["module"])
                same_namespace_block = module_parent_namespace(dependency_module) == consumer_parent_namespace
                if same_namespace_block and token == str(decl["basename"]) and token_signature_hits >= 2:
                    confidence = "same_namespace_short_name"
                else:
                    confidence = "imported_unique_alias"

            if decl is None or confidence is None:
                continue

            dependency = str(decl["module"])
            hit = dep_hits.setdefault(dependency, {
                "dependency_module": dependency,
                "consumer_module": consumer,
                "reference_count": 0,
                "unique_symbol_count": 0,
                "confidence_counts": Counter(),
                "symbols": {},
            })
            symbol_name = str(decl["full_name"])
            symbol_entry = hit["symbols"].setdefault(symbol_name, {
                "symbol": symbol_name,
                "basename": str(decl["basename"]),
                "line": int(decl["line"]),
                "count": 0,
                "confidence_counts": Counter(),
                "aliases": set(),
            })
            hit["reference_count"] += count
            hit["confidence_counts"][confidence] += count
            symbol_entry["count"] += count
            symbol_entry["confidence_counts"][confidence] += count
            symbol_entry["aliases"].add(token)
            confidence_totals[confidence] += count
            referenced_symbol_names.add(symbol_name)

        referenced_modules = []
        for dependency, hit in sorted(dep_hits.items()):
            symbols = []
            for symbol_name, symbol_entry in sorted(hit["symbols"].items()):
                symbol_entry["aliases"] = sorted(symbol_entry["aliases"])
                symbol_entry["confidence_counts"] = dict(sorted(symbol_entry["confidence_counts"].items()))
                symbols.append(symbol_entry)
            hit["symbols"] = symbols
            hit["unique_symbol_count"] = len(symbols)
            hit["confidence_counts"] = dict(sorted(hit["confidence_counts"].items()))
            hit["sample_symbols"] = [s["symbol"] for s in symbols[:10]]
            referenced_modules.append(hit)
            semantic_dependency_adj[consumer].append(dependency)
            aggregated_edges.append({
                "consumer_module": consumer,
                "dependency_module": dependency,
                "reference_count": hit["reference_count"],
                "unique_symbol_count": hit["unique_symbol_count"],
                "confidence_counts": hit["confidence_counts"],
                "sample_symbols": hit["sample_symbols"],
            })
        semantic_dependency_adj[consumer] = sorted(set(semantic_dependency_adj[consumer]))
        module_usage[consumer] = {
            "consumer_module": consumer,
            "imported_module_count": len(imported_modules),
            "opened_namespace_count": len(open_namespaces_by_module.get(consumer, [])),
            "opened_namespaces": open_namespaces_by_module.get(consumer, []),
            "imported_alias_candidate_count": len(imported_alias_map),
            "opened_alias_candidate_count": len(opened_alias_map),
            "opened_imported_declaration_count": opened_imported_decl_counts.get(consumer, 0),
            "referenced_module_count": len(referenced_modules),
            "referenced_modules": referenced_modules,
        }

    symbol_dir = output_dir / "symbol_references"
    symbol_dir.mkdir(parents=True, exist_ok=True)

    declaration_payload = {
        "module_count": len(module_to_path),
        "declaration_count": sum(module_declaration_counts.values()),
        "modules": {
            module: {
                "declaration_count": len(declarations_by_module[module]),
                "open_namespaces": open_namespaces_by_module.get(module, []),
                "field_names": field_names_by_module.get(module, []),
                "declarations": declarations_by_module[module],
            }
            for module in sorted(module_to_path)
        },
    }
    references_payload = {
        "module_usage": module_usage,
        "edges": sorted(aggregated_edges, key=lambda x: (x["consumer_module"], x["dependency_module"])),
    }

    semantic_signal_edge_metadata = {
        (str(edge["dependency_module"]), str(edge["consumer_module"])): {
            "confidence_counts": dict(edge["confidence_counts"]),
            "reference_count": int(edge["reference_count"]),
            "unique_symbol_count": int(edge["unique_symbol_count"]),
            "sample_symbols": list(edge["sample_symbols"]),
            "weighted_score": float(sum(_CONFIDENCE_WEIGHTS.get(str(conf), 0) * int(count) for conf, count in edge["confidence_counts"].items())),
        }
        for edge in aggregated_edges
    }

    semantic_plan = compute_signal_plan(
        records,
        semantic_dependency_adj,
        symbol_dir,
        subdir="semantic_signal_plan",
        title="Semantic signal plan export",
        intro=(
            "This directory filters the dependency DAG through detected cross-module symbol references. "
            "It now combines exact qualified hits with conservative imported-alias and open-namespace heuristics."
        ),
        scope_note=(
            "This is still heuristic: it detects declarations, open namespaces and alias-like references syntactically. "
            "It is sharper than import-only analysis, but not a proof of semantic usage in Lean elaboration."
        ),
        signal_edge_metadata=semantic_signal_edge_metadata,
    )

    summary = {
        "module_count": len(module_to_path),
        "declaration_count": sum(module_declaration_counts.values()),
        "modules_with_declarations": sum(1 for n in module_declaration_counts.values() if n > 0),
        "modules_with_open_namespaces": sum(1 for namespaces in open_namespaces_by_module.values() if namespaces),
        "opened_namespace_count": sum(len(namespaces) for namespaces in open_namespaces_by_module.values()),
        "reference_edge_count": len(aggregated_edges),
        "consumer_module_count": sum(1 for payload in module_usage.values() if payload["referenced_module_count"] > 0),
        "referenced_dependency_module_count": len({edge["dependency_module"] for edge in aggregated_edges}),
        "referenced_symbol_count": len(referenced_symbol_names),
        "confidence_counts": dict(sorted(confidence_totals.items())),
        "files": {
            "declarations": "symbol_references/declarations.json",
            "references": "symbol_references/references.json",
            "semantic_signal_plan": "symbol_references/semantic_signal_plan/summary.json",
        },
        "semantic_signal_plan": {
            "edge_count": semantic_plan["edge_count"],
            "reduced_edge_count": semantic_plan["transitive_reduction"]["edge_count"],
            "mainline_length": semantic_plan["mainline"]["length"],
            "weighted_mainline_length": 0 if semantic_plan.get("weighted_mainline") is None else semantic_plan["weighted_mainline"]["length"],
            "weighted_mainline_score": 0.0 if semantic_plan.get("weighted_mainline") is None else semantic_plan["weighted_mainline"]["total_score"],
            "source_count": len(semantic_plan["sources"]),
            "sink_count": len(semantic_plan["sinks"]),
        },
    }

    write_json(symbol_dir / "summary.json", summary)
    write_json(symbol_dir / "declarations.json", declaration_payload)
    write_json(symbol_dir / "references.json", references_payload)
    readme_lines = [
        "# Symbol reference export",
        "",
        "This directory exports a heuristic symbol-level refinement of the import graph.",
        "",
        f"- Modules scanned: **{summary['module_count']}**",
        f"- Declarations detected: **{summary['declaration_count']}**",
        f"- Modules with open namespaces: **{summary['modules_with_open_namespaces']}**",
        f"- Opened namespaces detected: **{summary['opened_namespace_count']}**",
        f"- Symbol-reference edges: **{summary['reference_edge_count']}**",
        f"- Referenced symbols: **{summary['referenced_symbol_count']}**",
        f"- Confidence counts: `{summary['confidence_counts']}`",
        "",
        "## Files",
        "",
        "- `declarations.json`: detected declaration names and open namespaces per module",
        "- `references.json`: detected cross-module symbol references aggregated by consumer/dependency",
        "- `semantic_signal_plan/summary.json`: refined signal-plan export using only detected symbol-reference edges",
        "",
        "## Scope note",
        "",
        "The analysis remains conservative. It detects declarations, open namespaces and alias-like references syntactically; it does not run Lean elaboration and therefore cannot prove that every hit is semantically resolved exactly as detected.",
        "",
    ]
    (symbol_dir / "README.md").write_text("\n".join(readme_lines), encoding="utf-8")
    return {
        "summary": summary,
        "semantic_signal_plan": semantic_plan,
        "semantic_dependency_adj": semantic_dependency_adj,
        "semantic_signal_edge_metadata": semantic_signal_edge_metadata,
        "reference_edges": references_payload["edges"],
        "module_usage": module_usage,
        "open_namespaces_by_module": open_namespaces_by_module,
        "declarations_by_module": declarations_by_module,
        "field_names_by_module": field_names_by_module,
        "raw_text_by_module": raw_text_by_module,
        "module_to_path": module_to_path,
    }



def write_json(path: Path, payload: object) -> None:
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def write_csv(path: Path, header: list[str], rows: list[list[object]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(header)
        writer.writerows(rows)


def find_default_repo_root(script_path: Path) -> Path:
    """Return the default Lean repository root for the planning tool.

    The planning/documentation tool keeps the checked CNNA Lean tree under
    ``Repository/repo_snapshot/CNNA``.  Older packages expected the Lean tree at
    ``./CNNA``.  The default must therefore point at ``Repository/repo_snapshot``
    so module names are still derived as ``CNNA.*`` while the code may stay in
    place.

    Fallbacks preserve compatibility for ad-hoc standalone use.
    """
    tool_root = script_path.parent.parent
    candidates = [
        tool_root / "repo_snapshot",
        tool_root,
        Path.cwd() / "Repository" / "repo_snapshot",
        Path.cwd(),
    ]
    for candidate in candidates:
        if (candidate / "CNNA").is_dir():
            return candidate.resolve()
    return (tool_root / "repo_snapshot").resolve()


def find_default_output_dir(script_path: Path) -> Path:
    """Return the planning-tool inventory export directory.

    Inventory data is consumed by ``generate_tables.py`` from
    ``Repository/repo_inventory/raw_export``.  Keep that output location
    independent from the Lean source root.
    """
    return (script_path.parent.parent / "repo_inventory" / "raw_export").resolve()


def module_name_from_path(repo_root: Path, path: Path) -> str:
    rel = path.relative_to(repo_root)
    return ".".join(rel.with_suffix("").parts)


def collect_modules(repo_root: Path, source_root: Path) -> tuple[dict[str, Path], dict[str, dict[str, object]]]:
    module_to_path: dict[str, Path] = {}
    meta: dict[str, dict[str, object]] = {}
    for path in sorted(source_root.rglob("*.lean")):
        module = module_name_from_path(repo_root, path)
        module_to_path[module] = path
        rel = path.relative_to(repo_root)
        after_source_root = list(path.relative_to(source_root).with_suffix("").parts)
        meta[module] = {
            "relative_path": rel.as_posix(),
            "path_after_source_root": after_source_root,
            "is_build_module": path.stem == "BuildAll",
            "is_notation_module": path.stem == "Notation",
        }
    return module_to_path, meta


def classify_imports(imports: Iterable[str], internal_modules: set[str], internal_prefixes: tuple[str, ...]) -> tuple[list[str], list[str], list[str]]:
    internal: list[str] = []
    external: list[str] = []
    missing_internal: list[str] = []
    for mod in imports:
        if mod in internal_modules:
            internal.append(mod)
        elif any(mod == prefix or mod.startswith(prefix + ".") for prefix in internal_prefixes):
            missing_internal.append(mod)
        else:
            external.append(mod)
    return sorted(set(internal)), sorted(set(external)), sorted(set(missing_internal))


def reverse_edges(adjacency: dict[str, list[str]]) -> dict[str, list[str]]:
    rev: dict[str, set[str]] = defaultdict(set)
    for src, dsts in adjacency.items():
        for dst in dsts:
            rev[dst].add(src)
    return {k: sorted(v) for k, v in rev.items()}


def strongly_connected_components(nodes: list[str], adjacency: dict[str, list[str]]) -> list[list[str]]:
    sys.setrecursionlimit(max(10000, len(nodes) * 20))
    index = 0
    stack: list[str] = []
    on_stack: set[str] = set()
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    components: list[list[str]] = []

    def visit(v: str) -> None:
        nonlocal index
        indices[v] = index
        lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)
        for w in adjacency.get(v, []):
            if w not in indices:
                visit(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])
        if lowlink[v] == indices[v]:
            component: list[str] = []
            while stack:
                w = stack.pop()
                on_stack.remove(w)
                component.append(w)
                if w == v:
                    break
            if len(component) > 1 or (len(component) == 1 and component[0] in adjacency.get(component[0], [])):
                components.append(sorted(component))

    for node in nodes:
        if node not in indices:
            visit(node)
    return sorted(components, key=lambda xs: (len(xs), xs))


def topo_sort_dependency_first(nodes: list[str], dependency_adjacency: dict[str, list[str]]) -> tuple[list[str], list[list[str]]]:
    indegree = {n: len(dependency_adjacency.get(n, [])) for n in nodes}
    reverse_adj = reverse_edges(dependency_adjacency)
    queue = deque(sorted(n for n, deg in indegree.items() if deg == 0))
    order: list[str] = []
    while queue:
        node = queue.popleft()
        order.append(node)
        for importer in reverse_adj.get(node, []):
            indegree[importer] -= 1
            if indegree[importer] == 0:
                queue.append(importer)
    if len(order) == len(nodes):
        return order, []
    return order, strongly_connected_components(nodes, dependency_adjacency)


def topo_sort_forward(nodes: list[str], adjacency: dict[str, list[str]]) -> tuple[list[str], list[list[str]]]:
    indegree = {n: 0 for n in nodes}
    for src in nodes:
        for dst in adjacency.get(src, []):
            if dst in indegree:
                indegree[dst] += 1
    queue = deque(sorted(n for n, deg in indegree.items() if deg == 0))
    order: list[str] = []
    while queue:
        node = queue.popleft()
        order.append(node)
        for dst in adjacency.get(node, []):
            if dst in indegree:
                indegree[dst] -= 1
                if indegree[dst] == 0:
                    queue.append(dst)
    if len(order) == len(nodes):
        return order, []
    return order, strongly_connected_components(nodes, adjacency)


def transitive_closure(start: str, adjacency: dict[str, list[str]]) -> list[str]:
    seen: set[str] = set()
    stack = list(adjacency.get(start, []))
    while stack:
        node = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        stack.extend(adjacency.get(node, []))
    return sorted(seen)


def compute_all_reachability(nodes: list[str], adjacency: dict[str, list[str]], topo_order: list[str]) -> dict[str, set[str]]:
    reachable: dict[str, set[str]] = {n: set() for n in nodes}
    for node in reversed(topo_order):
        acc = reachable[node]
        for child in adjacency.get(node, []):
            acc.add(child)
            acc.update(reachable.get(child, set()))
    return reachable


def transitive_reduction_dag(nodes: list[str], adjacency: dict[str, list[str]], topo_order: list[str]) -> dict[str, list[str]]:
    reachable = compute_all_reachability(nodes, adjacency, topo_order)
    reduced: dict[str, list[str]] = {}
    for src in nodes:
        dsts = adjacency.get(src, [])
        kept: list[str] = []
        for dst in dsts:
            redundant = False
            for mid in dsts:
                if mid == dst:
                    continue
                if dst == mid or dst in reachable.get(mid, set()):
                    redundant = True
                    break
            if not redundant:
                kept.append(dst)
        reduced[src] = sorted(kept)
    return reduced


def compute_predecessors(nodes: list[str], adjacency: dict[str, list[str]]) -> dict[str, list[str]]:
    preds: dict[str, set[str]] = {n: set() for n in nodes}
    for src in nodes:
        for dst in adjacency.get(src, []):
            if dst in preds:
                preds[dst].add(src)
    return {k: sorted(v) for k, v in preds.items()}


def compute_topological_layers(nodes: list[str], adjacency: dict[str, list[str]], topo_order: list[str]) -> dict[str, int]:
    preds = compute_predecessors(nodes, adjacency)
    layer: dict[str, int] = {}
    for node in topo_order:
        node_preds = preds.get(node, [])
        layer[node] = 0 if not node_preds else 1 + max(layer[p] for p in node_preds)
    return layer


def compute_dominators(nodes: list[str], adjacency: dict[str, list[str]]) -> dict[str, object]:
    preds = compute_predecessors(nodes, adjacency)
    sources = sorted(n for n in nodes if not preds.get(n))
    super_source = "__signal_super_source__"
    all_nodes = [super_source] + list(nodes)
    dom: dict[str, set[str]] = {n: set(all_nodes) for n in nodes}
    dom[super_source] = {super_source}
    for src in sources:
        preds[src] = [super_source]
    changed = True
    while changed:
        changed = False
        for n in nodes:
            pred_list = preds.get(n, [])
            if not pred_list:
                new_dom = {n}
            else:
                intersection = set(all_nodes)
                for p in pred_list:
                    intersection &= dom[p]
                new_dom = intersection | {n}
            if new_dom != dom[n]:
                dom[n] = new_dom
                changed = True

    idom: dict[str, str | None] = {}
    for n in nodes:
        strict = dom[n] - {n}
        if not strict:
            idom[n] = None
            continue
        candidates = []
        for d in strict:
            if all(d == other or d not in dom[other] for other in strict):
                candidates.append(d)
        if not candidates:
            deepest = sorted(strict, key=lambda x: (len(dom[x]), x), reverse=True)
            chosen = deepest[0]
        else:
            chosen = sorted(candidates, key=lambda x: (x == super_source, x))[0]
        idom[n] = None if chosen == super_source else chosen

    tree_children: dict[str, list[str]] = defaultdict(list)
    for n, parent in idom.items():
        if parent is None:
            continue
        tree_children[parent].append(n)
    return {
        "sources": sources,
        "dominators": {n: sorted(x for x in dom[n] if x != super_source) for n in nodes},
        "immediate_dominators": idom,
        "dominator_tree": {k: sorted(v) for k, v in tree_children.items()},
    }


def compute_best_source_paths(nodes: list[str], adjacency: dict[str, list[str]], topo_order: list[str]) -> dict[str, list[str]]:
    preds = compute_predecessors(nodes, adjacency)
    best: dict[str, list[str]] = {}
    for node in topo_order:
        pred_list = preds.get(node, [])
        if not pred_list:
            best[node] = [node]
            continue
        candidates = [best[p] + [node] for p in pred_list if p in best]
        if not candidates:
            best[node] = [node]
            continue
        candidates.sort(key=lambda xs: (-len(xs), xs))
        best[node] = candidates[0]
    return best


def edge_list_from_adjacency(adjacency: dict[str, list[str]]) -> list[dict[str, str]]:
    return [{"source": src, "target": dst} for src, dsts in sorted(adjacency.items()) for dst in dsts]


def compute_top_dominator_modules(
    nodes: list[str],
    adjacency: dict[str, list[str]],
    preds: dict[str, list[str]],
    layers: dict[str, int],
    dominators: dict[str, object],
    rec_by_module: dict[str, ModuleRecord],
    sources: list[str],
    sinks: list[str],
) -> list[dict[str, object]]:
    dom_sets = dominators.get("dominators", {}) if isinstance(dominators, dict) else {}
    dom_tree = dominators.get("dominator_tree", {}) if isinstance(dominators, dict) else {}
    dominated_counts: Counter[str] = Counter()
    for node, doms in dom_sets.items():
        if not isinstance(doms, list):
            continue
        for dominator in doms:
            if dominator != node:
                dominated_counts[str(dominator)] += 1
    rows = []
    source_set = set(sources)
    sink_set = set(sinks)
    for node in nodes:
        rows.append({
            "module": node,
            "group": rec_by_module[node].group,
            "dominated_node_count": dominated_counts[node],
            "immediate_dominator_child_count": len(dom_tree.get(node, [])) if isinstance(dom_tree, dict) else 0,
            "signal_out_degree": len(adjacency.get(node, [])),
            "signal_in_degree": len(preds.get(node, [])),
            "layer": layers.get(node, 0),
            "is_source": node in source_set,
            "is_sink": node in sink_set,
        })
    rows.sort(key=lambda item: (-int(item["dominated_node_count"]), -int(item["immediate_dominator_child_count"]), -int(item["signal_out_degree"]), int(item["layer"]), str(item["module"])))
    return rows


def compute_bridge_rankings(
    bridge_summary: list[dict[str, object]],
    rec_by_module: dict[str, ModuleRecord],
) -> dict[str, object]:
    module_counter: Counter[str] = Counter()
    module_source_counter: Counter[str] = Counter()
    module_target_counter: Counter[str] = Counter()
    edge_map: dict[tuple[str, str], dict[str, object]] = {}
    pair_rankings: list[dict[str, object]] = []

    for bridge in bridge_summary:
        source_discipline = str(bridge.get("source_discipline"))
        target_discipline = str(bridge.get("target_discipline"))
        edge_count = int(bridge.get("edge_count", 0))
        pair_rankings.append({
            "source_discipline": source_discipline,
            "target_discipline": target_discipline,
            "edge_count": edge_count,
        })
        edges = bridge.get("edges")
        if not isinstance(edges, list):
            continue
        for edge in edges:
            if not isinstance(edge, dict):
                continue
            source = edge.get("source")
            target = edge.get("target")
            if not isinstance(source, str) or not isinstance(target, str):
                continue
            module_counter[source] += 1
            module_counter[target] += 1
            module_source_counter[source] += 1
            module_target_counter[target] += 1
            entry = edge_map.setdefault((source, target), {
                "source": source,
                "target": target,
                "source_group": rec_by_module[source].group if source in rec_by_module else None,
                "target_group": rec_by_module[target].group if target in rec_by_module else None,
                "count": 0,
                "source_disciplines": set(),
                "target_disciplines": set(),
                "discipline_pairs": set(),
            })
            entry["count"] += 1
            entry["source_disciplines"].add(source_discipline)
            entry["target_disciplines"].add(target_discipline)
            entry["discipline_pairs"].add((source_discipline, target_discipline))

    module_rankings = [
        {
            "module": module,
            "group": rec_by_module[module].group if module in rec_by_module else None,
            "bridge_participation_count": count,
            "as_source_count": module_source_counter[module],
            "as_target_count": module_target_counter[module],
        }
        for module, count in sorted(module_counter.items(), key=lambda item: (-item[1], item[0]))
    ]

    edge_rankings = []
    for entry in edge_map.values():
        edge_rankings.append({
            "source": entry["source"],
            "target": entry["target"],
            "source_group": entry["source_group"],
            "target_group": entry["target_group"],
            "count": entry["count"],
            "source_disciplines": sorted(entry["source_disciplines"]),
            "target_disciplines": sorted(entry["target_disciplines"]),
            "discipline_pairs": [
                {"source_discipline": src, "target_discipline": dst}
                for src, dst in sorted(entry["discipline_pairs"])
            ],
        })
    edge_rankings.sort(key=lambda item: (-int(item["count"]), str(item["source"]), str(item["target"])))
    pair_rankings.sort(key=lambda item: (-int(item["edge_count"]), str(item["source_discipline"]), str(item["target_discipline"])))

    return {
        "bridge_pair_rankings": pair_rankings,
        "bridge_module_rankings": module_rankings,
        "bridge_edge_rankings": edge_rankings,
    }



def summarize_signal_edge_confidence(meta: dict[str, object] | None) -> dict[str, object]:
    confidence_counts = meta.get("confidence_counts", {}) if isinstance(meta, dict) else {}
    if not isinstance(confidence_counts, dict):
        confidence_counts = {}
    weighted_score = float(meta.get("weighted_score", 0.0)) if isinstance(meta, dict) else 0.0
    strongest_confidence = None
    strongest_score = -1
    strongest_count = -1
    for key, value in confidence_counts.items():
        try:
            count = int(value)
        except Exception:
            continue
        score = _CONFIDENCE_WEIGHTS.get(str(key), 0)
        if score > strongest_score or (score == strongest_score and count > strongest_count) or (score == strongest_score and count == strongest_count and (strongest_confidence is None or str(key) < str(strongest_confidence))):
            strongest_confidence = str(key)
            strongest_score = score
            strongest_count = count
    return {
        "confidence_counts": dict(sorted((str(k), int(v)) for k, v in confidence_counts.items())),
        "weighted_score": weighted_score,
        "strongest_confidence": strongest_confidence,
        "strongest_confidence_weight": 0 if strongest_confidence is None else _CONFIDENCE_WEIGHTS.get(strongest_confidence, 0),
        "reference_count": int(meta.get("reference_count", 0)) if isinstance(meta, dict) else 0,
        "unique_symbol_count": int(meta.get("unique_symbol_count", 0)) if isinstance(meta, dict) else 0,
        "sample_symbols": list(meta.get("sample_symbols", [])) if isinstance(meta, dict) else [],
    }


def compute_best_weighted_source_paths(
    nodes: list[str],
    adjacency: dict[str, list[str]],
    topo_order: list[str],
    signal_edge_metadata: dict[tuple[str, str], dict[str, object]],
) -> dict[str, dict[str, object]]:
    preds = compute_predecessors(nodes, adjacency)
    best: dict[str, dict[str, object]] = {}
    for node in topo_order:
        pred_list = preds.get(node, [])
        if not pred_list:
            best[node] = {
                "path": [node],
                "score": 0.0,
                "edge_count": 0,
                "confidence_counts": {},
            }
            continue
        candidates: list[dict[str, object]] = []
        for pred in pred_list:
            if pred not in best:
                continue
            prev = best[pred]
            meta = summarize_signal_edge_confidence(signal_edge_metadata.get((pred, node), {}))
            confidence_counts = Counter(prev.get("confidence_counts", {}))
            confidence_counts.update(meta["confidence_counts"])
            candidates.append({
                "path": list(prev["path"]) + [node],
                "score": float(prev.get("score", 0.0)) + float(meta["weighted_score"]),
                "edge_count": int(prev.get("edge_count", 0)) + 1,
                "confidence_counts": dict(confidence_counts),
            })
        if not candidates:
            best[node] = {
                "path": [node],
                "score": 0.0,
                "edge_count": 0,
                "confidence_counts": {},
            }
            continue
        candidates.sort(key=lambda item: (-float(item["score"]), -int(item["edge_count"]), list(item["path"])))
        best[node] = candidates[0]
    return best


def compute_mainline_mismatch_report(
    syntactic_signal_plan: dict[str, object],
    semantic_signal_plan: dict[str, object] | None,
    semantic_edge_metadata: dict[tuple[str, str], dict[str, object]] | None,
    rec_by_module: dict[str, ModuleRecord],
) -> dict[str, object] | None:
    if semantic_signal_plan is None:
        return None
    syntactic_path = list(syntactic_signal_plan.get("mainline", {}).get("path", []))
    semantic_path = list(semantic_signal_plan.get("mainline", {}).get("path", []))
    weighted_path = list((semantic_signal_plan.get("weighted_mainline") or {}).get("path", []))
    syntactic_edges = [(syntactic_path[i], syntactic_path[i + 1]) for i in range(max(0, len(syntactic_path) - 1))]
    semantic_edge_set = {
        (str(edge.get("source")), str(edge.get("target")))
        for edge in semantic_signal_plan.get("mainline", {}).get("edges", [])
        if isinstance(edge, dict) and isinstance(edge.get("source"), str) and isinstance(edge.get("target"), str)
    }
    weighted_edge_set = {
        (str(edge.get("source")), str(edge.get("target")))
        for edge in (semantic_signal_plan.get("weighted_mainline") or {}).get("edges", [])
        if isinstance(edge, dict) and isinstance(edge.get("source"), str) and isinstance(edge.get("target"), str)
    }
    semantic_node_set = set(semantic_path)
    weighted_node_set = set(weighted_path)
    semantic_edge_metadata = semantic_edge_metadata or {}

    node_rows = []
    for node in syntactic_path:
        node_rows.append({
            "module": node,
            "group": rec_by_module[node].group if node in rec_by_module else None,
            "in_semantic_mainline": node in semantic_node_set,
            "in_weighted_semantic_mainline": node in weighted_node_set,
        })

    edge_rows = []
    missing_edges = 0
    weak_edges = 0
    for source, target in syntactic_edges:
        meta = summarize_signal_edge_confidence(semantic_edge_metadata.get((source, target)))
        present_semantic = (source, target) in semantic_edge_set
        present_weighted = (source, target) in weighted_edge_set
        if meta["reference_count"] == 0:
            missing_edges += 1
        elif meta["strongest_confidence_weight"] < _CONFIDENCE_WEIGHTS["qualified_suffix"]:
            weak_edges += 1
        edge_rows.append({
            "source": source,
            "target": target,
            "source_group": rec_by_module[source].group if source in rec_by_module else None,
            "target_group": rec_by_module[target].group if target in rec_by_module else None,
            "present_in_semantic_graph": meta["reference_count"] > 0,
            "present_in_semantic_mainline": present_semantic,
            "present_in_weighted_semantic_mainline": present_weighted,
            **meta,
        })

    return {
        "syntactic_mainline_length": len(syntactic_path),
        "semantic_mainline_length": len(semantic_path),
        "weighted_semantic_mainline_length": len(weighted_path),
        "syntactic_mainline_source": syntactic_path[0] if syntactic_path else None,
        "syntactic_mainline_sink": syntactic_path[-1] if syntactic_path else None,
        "semantic_mainline_source": semantic_path[0] if semantic_path else None,
        "semantic_mainline_sink": semantic_path[-1] if semantic_path else None,
        "weighted_semantic_mainline_source": weighted_path[0] if weighted_path else None,
        "weighted_semantic_mainline_sink": weighted_path[-1] if weighted_path else None,
        "shared_node_count_with_semantic_mainline": sum(1 for node in syntactic_path if node in semantic_node_set),
        "shared_node_count_with_weighted_mainline": sum(1 for node in syntactic_path if node in weighted_node_set),
        "shared_edge_count_with_semantic_mainline": sum(1 for edge in syntactic_edges if edge in semantic_edge_set),
        "shared_edge_count_with_weighted_mainline": sum(1 for edge in syntactic_edges if edge in weighted_edge_set),
        "syntactic_edges_missing_in_semantic_graph": missing_edges,
        "syntactic_edges_only_weakly_supported": weak_edges,
        "syntactic_only_nodes_vs_semantic_mainline": [node for node in syntactic_path if node not in semantic_node_set],
        "syntactic_only_nodes_vs_weighted_mainline": [node for node in syntactic_path if node not in weighted_node_set],
        "weighted_semantic_only_nodes": [node for node in weighted_path if node not in set(syntactic_path)],
        "node_coverage": node_rows,
        "edge_coverage": edge_rows,
    }


def compute_mainline_edge_forensics(
    syntactic_signal_plan: dict[str, object],
    semantic_signal_plan: dict[str, object] | None,
    semantic_edge_metadata: dict[tuple[str, str], dict[str, object]] | None,
    rec_by_module: dict[str, ModuleRecord],
    open_namespaces_by_module: dict[str, list[str]] | None,
    declarations_by_module: dict[str, list[dict[str, object]]] | None,
) -> dict[str, object] | None:
    if semantic_signal_plan is None:
        return None
    open_namespaces_by_module = open_namespaces_by_module or {}
    declarations_by_module = declarations_by_module or {}
    semantic_edge_metadata = semantic_edge_metadata or {}

    syntactic_path = list(syntactic_signal_plan.get("mainline", {}).get("path", []))
    semantic_edge_set = {
        (str(edge.get("source")), str(edge.get("target")))
        for edge in semantic_signal_plan.get("mainline", {}).get("edges", [])
        if isinstance(edge, dict) and isinstance(edge.get("source"), str) and isinstance(edge.get("target"), str)
    }
    weighted_edge_set = {
        (str(edge.get("source")), str(edge.get("target")))
        for edge in (semantic_signal_plan.get("weighted_mainline") or {}).get("edges", [])
        if isinstance(edge, dict) and isinstance(edge.get("source"), str) and isinstance(edge.get("target"), str)
    }

    module_basename_map = {
        module: sorted({str(decl.get("basename")) for decl in decls if isinstance(decl, dict) and decl.get("basename")})
        for module, decls in declarations_by_module.items()
    }
    module_parent_namespaces = {
        module: module.rsplit('.', 1)[0] if '.' in module else ''
        for module in rec_by_module
    }

    edge_rows = []
    status_counts = Counter()
    for i in range(max(0, len(syntactic_path) - 1)):
        source = syntactic_path[i]
        target = syntactic_path[i + 1]
        meta = summarize_signal_edge_confidence(semantic_edge_metadata.get((source, target)))
        strongest_weight = int(meta["strongest_confidence_weight"])
        if meta["reference_count"] == 0:
            status = "missing"
        elif strongest_weight < _CONFIDENCE_WEIGHTS["qualified_suffix"]:
            status = "weak"
        else:
            status = "strong"
        status_counts[status] += 1

        target_open_namespaces = sorted(open_namespaces_by_module.get(target, []))
        source_basenames = set(module_basename_map.get(source, []))
        target_basenames = set(module_basename_map.get(target, []))
        local_overlap = sorted(source_basenames & target_basenames)

        source_decls = declarations_by_module.get(source, [])
        source_alias_map = build_unique_alias_map_for_declarations(source_decls)
        opened_source_decls = [
            decl
            for decl in source_decls
            if any(
                str(decl.get("full_name")) == namespace
                or str(decl.get("full_name")).startswith(namespace + ".")
                or (decl.get("namespace") is not None and (str(decl.get("namespace")) == namespace or str(decl.get("namespace")).startswith(namespace + ".")))
                for namespace in target_open_namespaces
            )
        ]
        opened_source_alias_map = build_unique_alias_map_for_declarations(opened_source_decls)

        same_namespace_block = module_parent_namespaces.get(source, '') == module_parent_namespaces.get(target, '')
        likely_causes = []
        if local_overlap:
            likely_causes.append("local_name_shadowing_or_collision")
        if target_open_namespaces and len(opened_source_alias_map) > 0:
            likely_causes.append("open_namespace_resolution_surface")
        if len(source_alias_map) > 0:
            likely_causes.append("unqualified_import_alias_surface")
        if same_namespace_block:
            likely_causes.append("same_namespace_block")
        if status == "missing" and not likely_causes:
            likely_causes.append("structure_field_or_non_declaration_usage_likely")

        edge_rows.append({
            "source": source,
            "target": target,
            "source_group": rec_by_module[source].group if source in rec_by_module else None,
            "target_group": rec_by_module[target].group if target in rec_by_module else None,
            "status": status,
            "present_in_semantic_mainline": (source, target) in semantic_edge_set,
            "present_in_weighted_semantic_mainline": (source, target) in weighted_edge_set,
            "target_open_namespaces": target_open_namespaces,
            "local_declaration_overlap": local_overlap,
            "local_declaration_overlap_count": len(local_overlap),
            "source_alias_candidate_count": len(source_alias_map),
            "source_opened_alias_candidate_count": len(opened_source_alias_map),
            "same_namespace_block": same_namespace_block,
            "likely_causes": likely_causes,
            **meta,
        })

    return {
        "edge_count": len(edge_rows),
        "status_counts": dict(sorted(status_counts.items())),
        "edges": edge_rows,
    }


def compute_weak_mainline_edges(mainline_edge_forensics: dict[str, object] | None) -> dict[str, object] | None:
    if mainline_edge_forensics is None:
        return None
    edges = mainline_edge_forensics.get("edges")
    if not isinstance(edges, list):
        return None
    rows = []
    for edge in edges:
        if not isinstance(edge, dict):
            continue
        status = str(edge.get("status"))
        if status not in {"missing", "weak"}:
            continue
        strongest = edge.get("strongest_confidence")
        if status == "missing":
            priority = 100
            recommendation = "inspect target module for unqualified or non-declaration usage; consider explicit qualification or extending the forensic heuristic for fields/classes"
            category = "missing_semantic_edge"
        elif strongest == "anchored_open_namespace":
            priority = 40
            recommendation = "open-namespace usage appears anchored by direct import and signature surface; optional explicit qualification would harden it further"
            category = "benign_open_namespace"
        elif strongest == "open_namespace_alias":
            priority = 70
            recommendation = "prefer explicit qualification or narrower open namespaces for this handoff edge"
            category = "open_namespace_alias_only"
        elif strongest == "same_namespace_short_name":
            priority = 35
            recommendation = "same-namespace short-name usage appears benign; explicit qualification is optional for extra architectural clarity"
            category = "benign_same_namespace_short_name"
        elif strongest == "imported_unique_alias":
            priority = 60
            recommendation = "prefer stable qualified references or reduce alias ambiguity in the importing module"
            category = "imported_unique_alias_only"
        else:
            priority = 50
            recommendation = "inspect confidence mix and consider strengthening references with explicit names"
            category = f"{strongest}_only" if strongest else "weak_semantic_edge"
        rows.append({
            "priority": priority,
            "category": category,
            "recommendation": recommendation,
            **edge,
        })
    rows.sort(key=lambda item: (-int(item["priority"]), str(item["source"]), str(item["target"])))
    return {
        "edge_count": len(rows),
        "edges": rows,
    }


def sanitize_edge_slug(source: str, target: str) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "_", f"{source}__to__{target}").strip("_").lower()


def extract_line_windows(text: str, line_numbers: list[int], *, context_lines: int = 2, max_snippets: int = 5) -> list[dict[str, object]]:
    lines = text.splitlines()
    windows: list[dict[str, object]] = []
    seen: set[tuple[int, int]] = set()
    for line_no in sorted(set(int(n) for n in line_numbers if int(n) > 0)):
        start = max(1, line_no - context_lines)
        end = min(len(lines), line_no + context_lines)
        key = (start, end)
        if key in seen:
            continue
        seen.add(key)
        windows.append({
            "focus_line": line_no,
            "start_line": start,
            "end_line": end,
            "lines": [{"line": i, "text": lines[i - 1]} for i in range(start, end + 1)],
        })
        if len(windows) >= max_snippets:
            break
    return windows


def extract_term_snippets(text: str, terms: list[str], *, context_lines: int = 2, max_snippets: int = 5) -> list[dict[str, object]]:
    useful_terms = [term for term in terms if isinstance(term, str) and len(term.strip()) >= 3]
    if not useful_terms:
        return []
    lines = text.splitlines()
    hits: list[dict[str, object]] = []
    seen_windows: set[tuple[int, int]] = set()
    for idx, line in enumerate(lines, start=1):
        matched_terms = [term for term in useful_terms if term in line]
        if not matched_terms:
            continue
        start = max(1, idx - context_lines)
        end = min(len(lines), idx + context_lines)
        key = (start, end)
        if key in seen_windows:
            continue
        seen_windows.add(key)
        hits.append({
            "focus_line": idx,
            "matched_terms": matched_terms[:10],
            "start_line": start,
            "end_line": end,
            "lines": [{"line": i, "text": lines[i - 1]} for i in range(start, end + 1)],
        })
        if len(hits) >= max_snippets:
            break
    return hits


def extract_open_namespace_snippets(text: str, namespaces: list[str], *, context_lines: int = 1, max_snippets: int = 5) -> list[dict[str, object]]:
    if not namespaces:
        return []
    lines = text.splitlines()
    hits: list[dict[str, object]] = []
    seen_windows: set[tuple[int, int]] = set()
    namespace_terms = []
    for namespace in namespaces:
        namespace_terms.append(namespace)
        namespace_terms.append(namespace.split('.')[-1])
    for idx, line in enumerate(lines, start=1):
        if "open" not in line:
            continue
        matched = [term for term in namespace_terms if term and term in line]
        if not matched:
            continue
        start = max(1, idx - context_lines)
        end = min(len(lines), idx + context_lines)
        key = (start, end)
        if key in seen_windows:
            continue
        seen_windows.add(key)
        hits.append({
            "focus_line": idx,
            "matched_terms": matched[:10],
            "start_line": start,
            "end_line": end,
            "lines": [{"line": i, "text": lines[i - 1]} for i in range(start, end + 1)],
        })
        if len(hits) >= max_snippets:
            break
    return hits


def compute_edge_case_reports(
    mainline_edge_forensics: dict[str, object] | None,
    weak_mainline_edges: dict[str, object] | None,
    rec_by_module: dict[str, ModuleRecord],
    symbol_reference_export_context: dict[str, object] | None,
) -> dict[str, object] | None:
    if mainline_edge_forensics is None:
        return None
    edges = mainline_edge_forensics.get("edges")
    if not isinstance(edges, list):
        return None
    weak_lookup: dict[tuple[str, str], dict[str, object]] = {}
    if weak_mainline_edges is not None and isinstance(weak_mainline_edges.get("edges"), list):
        weak_lookup = {
            (str(edge.get("source")), str(edge.get("target"))): edge
            for edge in weak_mainline_edges["edges"]
            if isinstance(edge, dict) and isinstance(edge.get("source"), str) and isinstance(edge.get("target"), str)
        }

    module_usage = {} if symbol_reference_export_context is None else symbol_reference_export_context.get("module_usage", {})
    open_namespaces_by_module = {} if symbol_reference_export_context is None else symbol_reference_export_context.get("open_namespaces_by_module", {})
    declarations_by_module = {} if symbol_reference_export_context is None else symbol_reference_export_context.get("declarations_by_module", {})
    field_names_by_module = {} if symbol_reference_export_context is None else symbol_reference_export_context.get("field_names_by_module", {})
    raw_text_by_module = {} if symbol_reference_export_context is None else symbol_reference_export_context.get("raw_text_by_module", {})
    module_to_path = {} if symbol_reference_export_context is None else symbol_reference_export_context.get("module_to_path", {})

    reports: list[dict[str, object]] = []
    missing_reports: list[dict[str, object]] = []
    weak_reports: list[dict[str, object]] = []

    for edge in edges:
        if not isinstance(edge, dict):
            continue
        status = str(edge.get("status"))
        if status not in {"missing", "weak"}:
            continue
        source = str(edge.get("source"))
        target = str(edge.get("target"))
        target_usage = module_usage.get(target, {}) if isinstance(module_usage, dict) else {}
        referenced_modules = target_usage.get("referenced_modules", []) if isinstance(target_usage, dict) else []
        dependency_detail = None
        if isinstance(referenced_modules, list):
            for item in referenced_modules:
                if isinstance(item, dict) and item.get("dependency_module") == source:
                    dependency_detail = item
                    break

        source_decls = declarations_by_module.get(source, []) if isinstance(declarations_by_module, dict) else []
        source_basenames = sorted({str(decl.get("basename")) for decl in source_decls if isinstance(decl, dict) and decl.get("basename")})
        if dependency_detail is not None:
            symbol_rows = dependency_detail.get("symbols", []) if isinstance(dependency_detail.get("symbols"), list) else []
            relevant_symbol_names = [str(symbol.get("symbol")) for symbol in symbol_rows if isinstance(symbol, dict) and symbol.get("symbol")]
            relevant_basenames = sorted({str(symbol.get("basename")) for symbol in symbol_rows if isinstance(symbol, dict) and symbol.get("basename")})
            relevant_aliases = sorted({str(alias) for symbol in symbol_rows if isinstance(symbol, dict) for alias in symbol.get("aliases", []) if isinstance(alias, str)})
            source_line_numbers = [int(symbol.get("line")) for symbol in symbol_rows if isinstance(symbol, dict) and isinstance(symbol.get("line"), int)]
        else:
            relevant_symbol_names = []
            relevant_basenames = source_basenames[:12]
            relevant_aliases = []
            source_line_numbers = [int(decl.get("line")) for decl in source_decls[:6] if isinstance(decl, dict) and isinstance(decl.get("line"), int)]

        target_open_namespaces = list(open_namespaces_by_module.get(target, [])) if isinstance(open_namespaces_by_module, dict) else []
        target_text = str(raw_text_by_module.get(target, "")) if isinstance(raw_text_by_module, dict) else ""
        source_text = str(raw_text_by_module.get(source, "")) if isinstance(raw_text_by_module, dict) else ""

        source_field_names = list(field_names_by_module.get(source, [])) if isinstance(field_names_by_module, dict) else []
        target_search_terms = list(dict.fromkeys(relevant_aliases + relevant_basenames + [name.split('.')[-1] for name in relevant_symbol_names]))
        projection_terms = list(dict.fromkeys([f".{name}" for name in source_field_names[:20]] + source_field_names[:20]))
        source_decl_snippets = extract_line_windows(source_text, source_line_numbers, context_lines=2, max_snippets=5)
        target_reference_snippets = extract_term_snippets(target_text, target_search_terms, context_lines=2, max_snippets=5)
        target_open_snippets = extract_open_namespace_snippets(target_text, target_open_namespaces, context_lines=1, max_snippets=5)
        target_projection_snippets = extract_term_snippets(target_text, projection_terms, context_lines=2, max_snippets=5)

        probable_failure_modes = list(edge.get("likely_causes", [])) if isinstance(edge.get("likely_causes"), list) else []
        if status == "missing" and dependency_detail is None:
            probable_failure_modes.append("no_detected_dependency_detail")
        if status == "missing" and target_projection_snippets:
            probable_failure_modes.append("projection_or_field_surface_detected")
        if status == "weak" and edge.get("strongest_confidence") == "imported_unique_alias":
            probable_failure_modes.append("alias_only_support")
        if status == "weak" and edge.get("strongest_confidence") == "open_namespace_alias":
            probable_failure_modes.append("open_namespace_only_support")

        suggested_actions = []
        if status == "missing":
            suggested_actions.extend([
                "Inspect the target module for structure-field, class-field or theorem-application usage that does not surface as a declaration token.",
                "Consider explicitly qualifying at least one core source symbol in the target module to harden the semantic edge.",
            ])
        elif edge.get("strongest_confidence") == "open_namespace_alias":
            suggested_actions.extend([
                "Prefer explicit qualification for the handoff-critical symbol(s).",
                "Reduce broad `open` surfaces in the target module if possible.",
            ])
        elif edge.get("strongest_confidence") == "imported_unique_alias":
            suggested_actions.extend([
                "Prefer stable qualified references or add one explicit anchoring reference on this edge.",
                "Check whether the importing module relies on short aliases that could be made architecturally explicit.",
            ])
        else:
            suggested_actions.append("Inspect the target usage surface and strengthen references where the mainline matters architecturally.")

        report = {
            "slug": sanitize_edge_slug(source, target),
            "status": status,
            "source": source,
            "target": target,
            "source_group": rec_by_module[source].group if source in rec_by_module else None,
            "target_group": rec_by_module[target].group if target in rec_by_module else None,
            "source_path": None if source not in module_to_path else str(module_to_path[source]),
            "target_path": None if target not in module_to_path else str(module_to_path[target]),
            "confidence": {
                "strongest_confidence": edge.get("strongest_confidence"),
                "strongest_confidence_weight": edge.get("strongest_confidence_weight"),
                "confidence_counts": edge.get("confidence_counts", {}),
                "weighted_score": edge.get("weighted_score", 0.0),
                "reference_count": edge.get("reference_count", 0),
                "unique_symbol_count": edge.get("unique_symbol_count", 0),
            },
            "edge_forensics": edge,
            "weak_edge_summary": weak_lookup.get((source, target)),
            "dependency_detail": dependency_detail,
            "probable_failure_modes": sorted(dict.fromkeys(str(mode) for mode in probable_failure_modes)),
            "suggested_actions": suggested_actions,
            "snippet_terms": {
                "relevant_symbol_names": relevant_symbol_names[:20],
                "relevant_basenames": relevant_basenames[:20],
                "relevant_aliases": relevant_aliases[:20],
                "source_field_names": source_field_names[:20],
                "target_open_namespaces": target_open_namespaces[:20],
            },
            "snippets": {
                "source_declarations": source_decl_snippets,
                "target_reference_surface": target_reference_snippets,
                "target_open_namespace_surface": target_open_snippets,
                "target_projection_surface": target_projection_snippets,
            },
        }
        reports.append(report)
        if status == "missing":
            missing_reports.append(report)
        else:
            weak_reports.append(report)

    reports.sort(key=lambda item: (0 if item["status"] == "missing" else 1, str(item["source"]), str(item["target"])))
    missing_reports.sort(key=lambda item: (str(item["source"]), str(item["target"])))
    weak_reports.sort(key=lambda item: (str(item["source"]), str(item["target"])))
    return {
        "report_count": len(reports),
        "missing_report_count": len(missing_reports),
        "weak_report_count": len(weak_reports),
        "reports": reports,
        "missing_reports": missing_reports,
        "weak_reports": weak_reports,
    }


def classify_sink_taxonomy_entry(module: str, rec_by_module: dict[str, ModuleRecord]) -> dict[str, object]:
    group = rec_by_module[module].group if module in rec_by_module else None
    classification = "ambiguous_leaf"
    rationale = "No dedicated rule matched."
    if ".Handoff.Inputs." in module or re.search(r"\.Handoff\.Outputs\.A_to_[A-Z]$", module):
        classification = "intentional_output"
        rationale = "Explicit handoff input/output leaf."
    elif ".ProofObligation" in module or module.endswith(".Completion") or module.endswith(".Preparation"):
        classification = "proof_obligation_terminal"
        rationale = "Proof-obligation closure/preparation leaf."
    elif "Research" in module or "Readiness" in module:
        classification = "research_leaf"
        rationale = "Research/readiness leaf by module naming."
    elif module.startswith("CNNA.PillarA.Foundation.") and (module.endswith("Lemmas") or module.endswith("Analysis") or module.endswith("Bridge")):
        classification = "foundation_aux_leaf"
        rationale = "Foundation auxiliary/analysis leaf."
    elif module.startswith("CNNA.PillarA.Geometry.") or module.startswith("CNNA.PillarA.Network.") or module.startswith("CNNA.PillarA.Finite.") or module.startswith("CNNA.PillarA.ToC.") or module.startswith("CNNA.Structural.CayleyDickson."):
        classification = "diagnostic_leaf"
        rationale = "Domain-side branch leaf outside explicit handoff outputs."
    return {
        "module": module,
        "group": group,
        "classification": classification,
        "rationale": rationale,
    }


def compute_sink_taxonomy(syntactic_signal_plan: dict[str, object], rec_by_module: dict[str, ModuleRecord]) -> dict[str, object]:
    sinks = list(syntactic_signal_plan.get("sinks", []))
    entries = [classify_sink_taxonomy_entry(module, rec_by_module) for module in sinks]
    counts = Counter(entry["classification"] for entry in entries)
    entries.sort(key=lambda item: (str(item["classification"]), str(item["module"])))
    return {
        "sink_count": len(entries),
        "classification_counts": dict(sorted(counts.items())),
        "entries": entries,
    }


def compute_trunk_vs_extensions(
    core_records: list[ModuleRecord],
    semantic_dependency_adj: dict[str, list[str]] | None,
    semantic_signal_edge_metadata: dict[tuple[str, str], dict[str, object]] | None,
    syntactic_signal_plan: dict[str, object],
    semantic_signal_plan: dict[str, object] | None,
    output_dir: Path,
    *,
    minimum_confidence_weight: int = 3,
) -> dict[str, object] | None:
    if semantic_dependency_adj is None or semantic_signal_edge_metadata is None or semantic_signal_plan is None:
        return None
    confidence_names = sorted(name for name, weight in _CONFIDENCE_WEIGHTS.items() if weight >= minimum_confidence_weight)
    robust_dependency_adj: dict[str, list[str]] = {}
    robust_edge_metadata: dict[tuple[str, str], dict[str, object]] = {}
    heuristic_edges = []
    for consumer, dependencies in semantic_dependency_adj.items():
        kept = []
        for dependency in dependencies:
            meta = semantic_signal_edge_metadata.get((dependency, consumer), {})
            info = summarize_signal_edge_confidence(meta)
            if int(info["strongest_confidence_weight"]) >= minimum_confidence_weight:
                kept.append(dependency)
                robust_edge_metadata[(dependency, consumer)] = meta
            else:
                heuristic_edges.append({
                    "source": dependency,
                    "target": consumer,
                    **info,
                })
        robust_dependency_adj[consumer] = sorted(set(kept))
    robust_plan = compute_signal_plan(
        core_records,
        robust_dependency_adj,
        output_dir,
        subdir="architectural_core/robust_semantic_signal_plan",
        title="Architectural core robust semantic signal plan",
        intro=(
            "This directory restricts the clean semantic graph to edges at or above the configured minimum confidence threshold. "
            "It highlights the robust trunk before heuristic extensions are added back."
        ),
        scope_note=(
            "This is still heuristic, but intentionally stricter than the full semantic graph."
        ),
        signal_edge_metadata=robust_edge_metadata,
    )
    weighted_mainline_edges = {(str(edge.get("source")), str(edge.get("target"))) for edge in (semantic_signal_plan.get("weighted_mainline") or {}).get("edges", []) if isinstance(edge, dict)}
    heuristic_edges.sort(key=lambda item: (0 if (item["source"], item["target"]) in weighted_mainline_edges else 1, int(item["strongest_confidence_weight"]), str(item["source"]), str(item["target"])))
    robust_edge_set = set(robust_edge_metadata)
    syntactic_mainline_edges = {(edge["source"], edge["target"]) for edge in syntactic_signal_plan.get("mainline", {}).get("edges", []) if isinstance(edge, dict)}
    return {
        "minimum_confidence_weight": minimum_confidence_weight,
        "minimum_confidence_classes": confidence_names,
        "robust_edge_count": len(robust_edge_metadata),
        "heuristic_edge_count": len(heuristic_edges),
        "robust_trunk": {
            "mainline_length": robust_plan["mainline"]["length"],
            "weighted_mainline_length": 0 if robust_plan.get("weighted_mainline") is None else robust_plan["weighted_mainline"]["length"],
            "source_count": len(robust_plan["sources"]),
            "sink_count": len(robust_plan["sinks"]),
            "summary_file": "architectural_core/robust_semantic_signal_plan/summary.json",
        },
        "syntactic_mainline_edges_supported_robustly": sorted(
            {f"{src} -> {dst}" for (src, dst) in syntactic_mainline_edges if (src, dst) in robust_edge_set}
        ),
        "heuristic_extensions": heuristic_edges,
    }


def compute_signal_plan(
    records: list[ModuleRecord],
    dependency_adj: dict[str, list[str]],
    output_dir: Path,
    *,
    subdir: str = "signal_plan",
    title: str = "Signal plan export",
    intro: str = "This directory interprets the import DAG as a forward signal graph: dependency modules feed the modules that import them.",
    scope_note: str = "This is a syntactic signal plan derived from imports. It does not prove semantic handoff usage at symbol level.",
    signal_edge_metadata: dict[tuple[str, str], dict[str, object]] | None = None,
) -> dict[str, object]:
    nodes = sorted(r.module for r in records)
    rec_by_module = {r.module: r for r in records}
    signal_adj = reverse_edges(dependency_adj)
    for node in nodes:
        signal_adj.setdefault(node, [])
    topo_order, cycles = topo_sort_forward(nodes, signal_adj)
    preds = compute_predecessors(nodes, signal_adj)
    sources = sorted(n for n in nodes if not preds.get(n))
    sinks = sorted(n for n in nodes if not signal_adj.get(n))
    layers = compute_topological_layers(nodes, signal_adj, topo_order) if not cycles else {n: 0 for n in nodes}

    reduced_adj = transitive_reduction_dag(nodes, signal_adj, topo_order) if not cycles else {n: list(signal_adj.get(n, [])) for n in nodes}
    reduced_preds = compute_predecessors(nodes, reduced_adj)
    reduced_sources = sorted(n for n in nodes if not reduced_preds.get(n))
    reduced_sinks = sorted(n for n in nodes if not reduced_adj.get(n))

    dominators = compute_dominators(nodes, signal_adj) if not cycles else {
        "sources": sources,
        "dominators": {n: [] for n in nodes},
        "immediate_dominators": {n: None for n in nodes},
        "dominator_tree": {},
    }

    best_paths = compute_best_source_paths(nodes, signal_adj, topo_order) if not cycles else {n: [n] for n in nodes}
    critical_sink_paths = []
    for sink in sinks:
        path = best_paths.get(sink, [sink])
        critical_sink_paths.append({
            "sink": sink,
            "path": path,
            "source": path[0] if path else sink,
            "length": len(path),
            "sink_group": rec_by_module[sink].group,
        })
    critical_sink_paths.sort(key=lambda x: (-int(x["length"]), str(x["sink"]), list(x["path"])))

    mainline = critical_sink_paths[0]["path"] if critical_sink_paths else []
    mainline_nodes = set(mainline)
    mainline_edges = [{"source": mainline[i], "target": mainline[i + 1]} for i in range(len(mainline) - 1)]
    mainline_edge_set = {(e["source"], e["target"]) for e in mainline_edges}

    branch_nodes = [n for n in nodes if n not in mainline_nodes]
    branch_edges = [
        {"source": src, "target": dst}
        for src in nodes for dst in signal_adj.get(src, [])
        if (src, dst) not in mainline_edge_set
    ]

    mainline_attachments = []
    for node in branch_nodes:
        pred_list = preds.get(node, [])
        attached_from = sorted(p for p in pred_list if p in mainline_nodes)
        if not attached_from:
            doms = dominators.get("dominators", {}).get(node, [])
            attached_from = [d for d in doms if d in mainline_nodes]
        mainline_attachments.append({
            "node": node,
            "group": rec_by_module[node].group,
            "attached_from": attached_from,
            "layer": layers.get(node, 0),
        })
    mainline_attachments.sort(key=lambda x: (x["layer"], x["node"]))

    layer_buckets: dict[int, list[str]] = defaultdict(list)
    for node, layer in layers.items():
        layer_buckets[layer].append(node)

    top_dominators = compute_top_dominator_modules(
        nodes,
        signal_adj,
        preds,
        layers,
        dominators,
        rec_by_module,
        sources,
        sinks,
    ) if not cycles else []

    weighted_sink_paths: list[dict[str, object]] = []
    weighted_mainline = None
    if signal_edge_metadata and not cycles:
        best_weighted_paths = compute_best_weighted_source_paths(nodes, signal_adj, topo_order, signal_edge_metadata)
        for sink in sinks:
            best = best_weighted_paths.get(sink, {"path": [sink], "score": 0.0, "edge_count": 0, "confidence_counts": {}})
            path = list(best.get("path", [sink]))
            edge_details = []
            for i in range(max(0, len(path) - 1)):
                source = path[i]
                target = path[i + 1]
                meta = summarize_signal_edge_confidence(signal_edge_metadata.get((source, target)))
                edge_details.append({"source": source, "target": target, **meta})
            weighted_sink_paths.append({
                "sink": sink,
                "source": path[0] if path else sink,
                "path": path,
                "length": len(path),
                "edge_count": int(best.get("edge_count", 0)),
                "total_score": float(best.get("score", 0.0)),
                "average_edge_score": 0.0 if not edge_details else float(best.get("score", 0.0)) / len(edge_details),
                "confidence_counts": dict(sorted((str(k), int(v)) for k, v in dict(best.get("confidence_counts", {})).items())),
                "edge_details": edge_details,
            })
        weighted_sink_paths.sort(key=lambda item: (-float(item["total_score"]), -int(item["length"]), str(item["sink"]), list(item["path"])))
        if weighted_sink_paths:
            top_weighted = weighted_sink_paths[0]
            weighted_mainline = {
                "path": top_weighted["path"],
                "length": top_weighted["length"],
                "edge_count": top_weighted["edge_count"],
                "total_score": top_weighted["total_score"],
                "average_edge_score": top_weighted["average_edge_score"],
                "source": top_weighted["source"],
                "sink": top_weighted["sink"],
                "confidence_counts": top_weighted["confidence_counts"],
                "groups": [rec_by_module[m].group for m in top_weighted["path"]],
                "edges": [
                    {
                        "source": edge["source"],
                        "target": edge["target"],
                        "confidence_counts": edge["confidence_counts"],
                        "weighted_score": edge["weighted_score"],
                        "strongest_confidence": edge["strongest_confidence"],
                        "strongest_confidence_weight": edge["strongest_confidence_weight"],
                        "reference_count": edge["reference_count"],
                        "unique_symbol_count": edge["unique_symbol_count"],
                        "sample_symbols": edge["sample_symbols"],
                    }
                    for edge in top_weighted["edge_details"]
                ],
            }

    payload = {
        "node_count": len(nodes),
        "edge_count": sum(len(v) for v in signal_adj.values()),
        "acyclic": not bool(cycles),
        "cycles": cycles,
        "sources": sources,
        "sinks": sinks,
        "topological_order": topo_order,
        "layers": [{"layer": layer, "modules": sorted(mods)} for layer, mods in sorted(layer_buckets.items())],
        "signal_edges": edge_list_from_adjacency(signal_adj),
        "transitive_reduction": {
            "sources": reduced_sources,
            "sinks": reduced_sinks,
            "edge_count": sum(len(v) for v in reduced_adj.values()),
            "edges": edge_list_from_adjacency(reduced_adj),
        },
        "dominators": dominators,
        "top_dominators": top_dominators,
        "critical_sink_paths": critical_sink_paths,
        "weighted_sink_paths": weighted_sink_paths,
        "weighted_mainline": weighted_mainline,
        "mainline": {
            "path": mainline,
            "length": len(mainline),
            "source": mainline[0] if mainline else None,
            "sink": mainline[-1] if mainline else None,
            "groups": [rec_by_module[m].group for m in mainline],
            "edges": mainline_edges,
        },
        "side_branches": {
            "node_count": len(branch_nodes),
            "edge_count": len(branch_edges),
            "nodes": branch_nodes,
            "edges": branch_edges,
            "attachments": mainline_attachments,
        },
    }

    signal_dir = output_dir / subdir
    signal_dir.mkdir(parents=True, exist_ok=True)
    write_json(signal_dir / "summary.json", payload)
    write_json(signal_dir / "layers.json", payload["layers"])
    write_json(signal_dir / "dominators.json", dominators)
    write_json(signal_dir / "top_dominators.json", top_dominators)
    write_json(signal_dir / "source_sink_paths.json", critical_sink_paths)
    write_json(signal_dir / "mainline.json", payload["mainline"])
    if weighted_sink_paths:
        write_json(signal_dir / "weighted_source_sink_paths.json", weighted_sink_paths)
    if weighted_mainline is not None:
        write_json(signal_dir / "weighted_mainline.json", weighted_mainline)

    write_subgraph_dot(
        signal_dir / "signal_graph.dot",
        "signal_graph",
        nodes,
        signal_adj,
        {r.module: r.group for r in records},
    )
    write_subgraph_dot(
        signal_dir / "signal_graph_reduced.dot",
        "signal_graph_reduced",
        nodes,
        reduced_adj,
        {r.module: r.group for r in records},
    )

    readme_lines = [
        f"# {title}",
        "",
        intro,
        "",
        f"- Nodes: **{payload['node_count']}**",
        f"- Signal edges: **{payload['edge_count']}**",
        f"- Acyclic: **{payload['acyclic']}**",
        f"- Sources: **{len(sources)}**",
        f"- Sinks: **{len(sinks)}**",
        f"- Reduced edges: **{payload['transitive_reduction']['edge_count']}**",
        "",
        "## Mainline",
        "",
        f"- Source: `{payload['mainline']['source']}`" if payload["mainline"]["source"] else "- Source: none",
        f"- Sink: `{payload['mainline']['sink']}`" if payload["mainline"]["sink"] else "- Sink: none",
        f"- Length: **{payload['mainline']['length']}**",
        f"- Path: {' → '.join(f'`{m}`' for m in payload['mainline']['path']) if payload['mainline']['path'] else 'none'}",
        "",
        "## Critical source→sink paths",
        "",
    ]
    for item in critical_sink_paths[:20]:
        readme_lines.append(f"- `{item['source']}` → `{item['sink']}` ({item['length']} nodes)")
    if not critical_sink_paths:
        readme_lines.append("- none")
    readme_lines.extend([
        "",
        "## Files",
        "",
        "- `summary.json`: aggregated signal-plan export",
        "- `signal_graph.dot`: forward signal graph",
        "- `signal_graph_reduced.dot`: transitive reduction of the forward signal graph",
        "- `dominators.json`: dominator sets and immediate dominators",
        "- `source_sink_paths.json`: representative critical source→sink paths",
        "- `mainline.json`: selected longest mainline path",
        "- `layers.json`: topological signal layers",
        "- `weighted_source_sink_paths.json`: confidence-weighted source→sink paths" if weighted_sink_paths else "- weighted source→sink paths: not computed",
        "- `weighted_mainline.json`: confidence-weighted mainline" if weighted_mainline is not None else "- confidence-weighted mainline: not computed",
        "",
        "## Scope note",
        "",
        scope_note,
        "",
    ])
    (signal_dir / "README.md").write_text("\n".join(readme_lines), encoding="utf-8")
    return payload


def pick_group(path_after_source_root: list[str], depth: int) -> str:
    if not path_after_source_root:
        return "<root>"
    if len(path_after_source_root) == 1:
        return path_after_source_root[0]
    usable = path_after_source_root[:-1]
    if not usable:
        usable = path_after_source_root
    return "/".join(usable[: max(1, min(depth, len(usable)))])


def compute_group_summary(records: list[ModuleRecord], adjacency: dict[str, list[str]]) -> dict[str, object]:
    rec_by_module = {r.module: r for r in records}
    groups = sorted({r.group for r in records})
    per_group: dict[str, dict[str, object]] = {}
    for group in groups:
        modules = sorted(r.module for r in records if r.group == group)
        module_set = set(modules)
        internal_edges = sorted([
            {"source": src, "target": dst}
            for src in modules
            for dst in adjacency.get(src, [])
            if dst in module_set
        ], key=lambda x: (x["source"], x["target"]))
        outgoing_edges = sorted([
            {"source": src, "target": dst, "target_group": rec_by_module[dst].group}
            for src in modules
            for dst in adjacency.get(src, [])
            if dst not in module_set
        ], key=lambda x: (x["source"], x["target"]))
        incoming_edges = sorted([
            {"source": src, "target": dst, "source_group": rec_by_module[src].group}
            for src in rec_by_module
            for dst in adjacency.get(src, [])
            if dst in module_set and src not in module_set
        ], key=lambda x: (x["source"], x["target"]))
        per_group[group] = {
            "group": group,
            "module_count": len(modules),
            "modules": modules,
            "internal_edge_count": len(internal_edges),
            "outgoing_edge_count": len(outgoing_edges),
            "incoming_edge_count": len(incoming_edges),
            "internal_edges": internal_edges,
            "outgoing_edges": outgoing_edges,
            "incoming_edges": incoming_edges,
        }
    return {"group_count": len(groups), "groups": per_group}


def compute_hotspots(records: list[ModuleRecord], count: int) -> dict[str, object]:
    rows = []
    for r in records:
        rows.append({
            "module": r.module,
            "group": r.group,
            "internal_out_degree": len(r.internal_imports),
            "internal_in_degree": len(r.internal_imported_by),
            "total_internal_degree": len(r.internal_imports) + len(r.internal_imported_by),
            "total_imports": len(r.imports),
            "transitive_internal_imports": len(r.transitive_internal_imports),
            "is_build_module": r.is_build_module,
            "is_notation_module": r.is_notation_module,
        })
    def top_by(key: str) -> list[dict[str, object]]:
        return sorted(rows, key=lambda x: (-int(x[key]), str(x["module"])))[:count]
    return {
        "top_internal_out_degree": top_by("internal_out_degree"),
        "top_internal_in_degree": top_by("internal_in_degree"),
        "top_total_internal_degree": top_by("total_internal_degree"),
        "top_transitive_internal_imports": top_by("transitive_internal_imports"),
    }


def write_dot(path: Path, nodes: list[str], module_to_path: dict[str, Path], internal_adjacency: dict[str, list[str]], raw_imports: dict[str, list[str]], internal_prefixes: tuple[str, ...]) -> None:
    def node_attrs(mod: str) -> str:
        stem = module_to_path[mod].stem
        attrs = ["shape=box"]
        if stem == "BuildAll":
            attrs.append('style="filled"')
            attrs.append('fillcolor="lightgoldenrod1"')
        elif stem == "Notation":
            attrs.append('style="filled"')
            attrs.append('fillcolor="lightcyan"')
        return ", ".join(attrs)

    lines = ["digraph LeanImports {", '  rankdir="LR";', '  node [fontsize=11];']
    for mod in nodes:
        lines.append(f'  "{mod}" [{node_attrs(mod)}];')
    for src in nodes:
        for dst in internal_adjacency.get(src, []):
            lines.append(f'  "{src}" -> "{dst}";')
    external_targets = sorted({dst for src in nodes for dst in raw_imports.get(src, []) if dst not in module_to_path})
    if external_targets:
        lines.append('  subgraph cluster_external {')
        lines.append('    label="External imports";')
        lines.append('    style=dashed;')
        for mod in external_targets:
            lines.append(f'    "{mod}" [shape=plaintext];')
        lines.append('  }')
        for src in nodes:
            for dst in raw_imports.get(src, []):
                if dst in module_to_path:
                    continue
                color = '"gray40"'
                if any(dst == prefix or dst.startswith(prefix + ".") for prefix in internal_prefixes):
                    color = '"red"'
                lines.append(f'  "{src}" -> "{dst}" [style=dashed, color={color}];')
    lines.append("}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_subgraph_dot(path: Path, graph_name: str, nodes: list[str], adjacency: dict[str, list[str]], node_groups: dict[str, str], bridges: list[dict[str, object]] | None = None) -> None:
    lines = [f"digraph {graph_name} {{", '  rankdir="LR";', '  node [shape=box, fontsize=11];']
    for node in nodes:
        label = node
        group = node_groups.get(node, "")
        attrs = []
        if group:
            attrs.append(f'tooltip="{group}"')
        lines.append(f'  "{label}" [{", ".join(attrs)}];' if attrs else f'  "{label}";')
    node_set = set(nodes)
    for src in nodes:
        for dst in adjacency.get(src, []):
            if dst in node_set:
                lines.append(f'  "{src}" -> "{dst}";')
    if bridges:
        for edge in bridges:
            src = str(edge["source"])
            dst = str(edge["target"])
            if src in node_set and dst not in node_set:
                lines.append(f'  "{dst}" [shape=plaintext];')
                lines.append(f'  "{src}" -> "{dst}" [style=dashed, color="blue"];')
            elif dst in node_set and src not in node_set:
                lines.append(f'  "{src}" [shape=plaintext];')
                lines.append(f'  "{src}" -> "{dst}" [style=dashed, color="darkgreen"];')
    lines.append("}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_markdown_summary(path: Path, repo_root: Path, source_root: Path, records: list[ModuleRecord], topo_order: list[str], cycles: list[list[str]], internal_prefixes: tuple[str, ...], warnings: list[str], signal_plan: dict[str, object] | None, symbol_reference_export: dict[str, object] | None, architectural_core_export: dict[str, object] | None) -> None:
    total_internal = sum(len(r.internal_imports) for r in records)
    total_external = sum(len(r.external_imports) for r in records)
    total_missing = sum(len(r.missing_internal_imports) for r in records)
    lines = [
        "# Lean module and import export",
        "",
        f"- Repo root: `{repo_root}`",
        f"- Source root: `{source_root}`",
        f"- Internal prefixes: `{', '.join(internal_prefixes)}`",
        f"- Modules: **{len(records)}**",
        f"- Internal import edges: **{total_internal}**",
        f"- External import edges: **{total_external}**",
        f"- Missing internal imports: **{total_missing}**",
        "",
    ]
    if signal_plan is not None:
        lines.extend([
            "## Signal-plan export",
            "",
            f"- Signal sources: **{len(signal_plan['sources'])}**",
            f"- Signal sinks: **{len(signal_plan['sinks'])}**",
            f"- Signal edges: **{signal_plan['edge_count']}**",
            f"- Reduced signal edges: **{signal_plan['transitive_reduction']['edge_count']}**",
            f"- Mainline length: **{signal_plan['mainline']['length']}**",
            f"- Files: `signal_plan/summary.json`, `signal_plan/signal_graph.dot`, `signal_plan/signal_graph_reduced.dot`",
            "",
        ])
    if symbol_reference_export is not None:
        summary = symbol_reference_export["summary"]
        lines.extend([
            "## Symbol-reference export",
            "",
            f"- Declarations detected: **{summary['declaration_count']}**",
            f"- Symbol-reference edges: **{summary['reference_edge_count']}**",
            f"- Referenced symbols: **{summary['referenced_symbol_count']}**",
            f"- Semantic signal edges: **{summary['semantic_signal_plan']['edge_count']}**",
            f"- Semantic mainline length: **{summary['semantic_signal_plan']['mainline_length']}**",
            f"- Files: `symbol_references/summary.json`, `symbol_references/references.json`, `symbol_references/semantic_signal_plan/summary.json`",
            "",
        ])
    if architectural_core_export is not None:
        summary = architectural_core_export["summary"]
        lines.extend([
            "## Architectural core export",
            "",
            f"- Artifact modules filtered: **{summary['artifact_module_count']}**",
            f"- Core modules retained: **{summary['core_module_count']}**",
            f"- Clean signal edges: **{summary['syntactic_signal_plan']['edge_count']}**",
            f"- Clean mainline length: **{summary['syntactic_signal_plan']['mainline_length']}**",
            f"- Clean semantic mainline length: **{summary['semantic_signal_plan']['mainline_length']}**" if summary['semantic_signal_plan'] is not None else "- Clean semantic mainline length: not computed",
            f"- Clean discipline bridges: **{summary['clean_discipline_bridges']['bridge_count']}**" if summary['clean_discipline_bridges'] is not None else "- Clean discipline bridges: not computed",
            f"- Files: `architectural_core/summary.json`, `architectural_core/artifact_modules.json`, `architectural_core/syntactic_signal_plan/summary.json`",
            "",
        ])
    if warnings:
        lines.append("## Validation warnings")
        lines.append("")
        for w in warnings:
            lines.append(f"- {w}")
        lines.append("")
    if cycles:
        lines.append("## Cycles detected")
        lines.append("")
        for idx, component in enumerate(cycles, start=1):
            lines.append(f"{idx}. `{', '.join(component)}`")
    else:
        lines.append("## Dependency-respecting topological order")
        lines.append("")
        for idx, mod in enumerate(topo_order, start=1):
            lines.append(f"{idx}. `{mod}`")
    lines.append("")
    lines.append("## Modules")
    lines.append("")
    for r in records:
        lines.extend([
            f"### `{r.module}`",
            "",
            f"- Group: `{r.group}`",
            f"- Path: `{r.path}`",
            f"- Imports ({len(r.imports)}): {', '.join(f'`{x}`' for x in r.imports) if r.imports else 'none'}",
            f"- Internal imports ({len(r.internal_imports)}): {', '.join(f'`{x}`' for x in r.internal_imports) if r.internal_imports else 'none'}",
            f"- External imports ({len(r.external_imports)}): {', '.join(f'`{x}`' for x in r.external_imports) if r.external_imports else 'none'}",
            f"- Missing internal imports ({len(r.missing_internal_imports)}): {', '.join(f'`{x}`' for x in r.missing_internal_imports) if r.missing_internal_imports else 'none'}",
            f"- Imported by ({len(r.imported_by)}): {', '.join(f'`{x}`' for x in r.imported_by) if r.imported_by else 'none'}",
            "",
        ])
    path.write_text("\n".join(lines), encoding="utf-8")


def slugify(name: str) -> str:
    slug = re.sub(r"[^a-zA-Z0-9]+", "_", name).strip("_")
    return slug.lower() or "discipline"




def classify_architecture_artifacts(records: list[ModuleRecord]) -> dict[str, object]:
    artifacts: dict[str, dict[str, object]] = {}
    reason_counts: Counter[str] = Counter()
    core_modules: list[str] = []

    for record in sorted(records, key=lambda r: r.module):
        reasons: list[str] = []
        if record.is_build_module:
            reasons.append("build_module")
        if record.is_notation_module:
            reasons.append("notation_module")
        if len(record.path_after_source_root) <= 1 and len(record.internal_imports) == 1 and record.internal_imports[0].endswith(".BuildAll"):
            reasons.append("top_level_umbrella")
        elif len(record.internal_imports) == 1 and record.internal_imports[0].endswith(".BuildAll") and not record.internal_imported_by:
            reasons.append("umbrella_module")
        if not record.internal_imports and not record.internal_imported_by:
            reasons.append("isolated_internal_module")
        if reasons:
            reason_counts.update(reasons)
            artifacts[record.module] = {
                "module": record.module,
                "group": record.group,
                "path": record.path,
                "reasons": reasons,
            }
        else:
            core_modules.append(record.module)

    return {
        "artifact_module_count": len(artifacts),
        "core_module_count": len(core_modules),
        "artifact_reason_counts": dict(sorted(reason_counts.items())),
        "artifact_modules": dict(sorted(artifacts.items())),
        "core_modules": sorted(core_modules),
    }



def restrict_records_and_adjacency(
    records: list[ModuleRecord],
    adjacency: dict[str, list[str]],
    kept_modules: set[str],
) -> tuple[list[ModuleRecord], dict[str, list[str]]]:
    filtered_records = [record for record in records if record.module in kept_modules]
    filtered_adj = {
        record.module: sorted(dst for dst in adjacency.get(record.module, []) if dst in kept_modules)
        for record in filtered_records
    }
    return filtered_records, filtered_adj



def compute_clean_discipline_bridge_summary(
    discipline_overview: dict[str, object] | None,
    kept_modules: set[str],
    rec_by_module: dict[str, ModuleRecord],
) -> dict[str, object] | None:
    if not discipline_overview:
        return None
    raw_bridges = discipline_overview.get("bridges")
    if not isinstance(raw_bridges, list):
        return None

    filtered_bridges: list[dict[str, object]] = []

    for raw_bridge in raw_bridges:
        if not isinstance(raw_bridge, dict):
            continue
        edges = raw_bridge.get("edges")
        if not isinstance(edges, list):
            continue
        kept_edges = [
            edge for edge in edges
            if isinstance(edge, dict)
            and isinstance(edge.get("source"), str)
            and isinstance(edge.get("target"), str)
            and edge["source"] in kept_modules
            and edge["target"] in kept_modules
        ]
        if not kept_edges:
            continue
        unique_modules = sorted({str(edge["source"]) for edge in kept_edges} | {str(edge["target"]) for edge in kept_edges})
        filtered_bridges.append({
            "source_discipline": raw_bridge.get("source_discipline"),
            "target_discipline": raw_bridge.get("target_discipline"),
            "edge_count": len(kept_edges),
            "edges": kept_edges,
            "bridge_modules": unique_modules,
        })

    filtered_bridges.sort(key=lambda item: (-int(item["edge_count"]), str(item.get("source_discipline")), str(item.get("target_discipline"))))
    bridge_rankings = compute_bridge_rankings(filtered_bridges, rec_by_module)

    return {
        "bridge_count": len(filtered_bridges),
        "bridges": filtered_bridges,
        "bridge_modules": bridge_rankings["bridge_module_rankings"],
        "bridge_rankings": bridge_rankings,
    }



def compute_architectural_core_export(
    records: list[ModuleRecord],
    dependency_adj: dict[str, list[str]],
    output_dir: Path,
    *,
    semantic_dependency_adj: dict[str, list[str]] | None = None,
    semantic_signal_edge_metadata: dict[tuple[str, str], dict[str, object]] | None = None,
    symbol_reference_export_context: dict[str, object] | None = None,
    discipline_overview: dict[str, object] | None = None,
) -> dict[str, object]:
    artifact_info = classify_architecture_artifacts(records)
    kept_modules = set(str(m) for m in artifact_info["core_modules"])
    rec_by_module = {record.module: record for record in records}

    core_records, core_dependency_adj = restrict_records_and_adjacency(records, dependency_adj, kept_modules)
    core_dir = output_dir / "architectural_core"
    core_dir.mkdir(parents=True, exist_ok=True)

    syntactic_signal_plan = compute_signal_plan(
        core_records,
        core_dependency_adj,
        output_dir,
        subdir="architectural_core/syntactic_signal_plan",
        title="Architectural core signal plan",
        intro=(
            "This directory filters out build, notation, umbrella and isolated artifact modules before computing the forward signal graph. "
            "It is meant as a cleaner architectural-core view, not as a replacement for the full raw export."
        ),
        scope_note=(
            "The raw signal plan remains the source of truth for exact import structure. "
            "This cleaned view is a diagnostic projection that tries to suppress aggregator artifacts."
        ),
    ) if core_records else {
        "node_count": 0,
        "edge_count": 0,
        "sources": [],
        "sinks": [],
        "transitive_reduction": {"edge_count": 0, "edges": [], "sources": [], "sinks": []},
        "mainline": {"length": 0, "path": [], "source": None, "sink": None, "groups": [], "edges": []},
    }

    semantic_signal_plan = None
    core_semantic_edge_metadata = None
    if semantic_dependency_adj is not None:
        core_semantic_records, core_semantic_adj = restrict_records_and_adjacency(records, semantic_dependency_adj, kept_modules)
        if semantic_signal_edge_metadata is not None:
            core_semantic_edge_metadata = {
                (source, target): meta
                for (source, target), meta in semantic_signal_edge_metadata.items()
                if source in kept_modules and target in kept_modules
            }
        semantic_signal_plan = compute_signal_plan(
            core_semantic_records,
            core_semantic_adj,
            output_dir,
            subdir="architectural_core/semantic_signal_plan",
            title="Architectural core semantic signal plan",
            intro=(
                "This directory applies the same artifact filter to the heuristic symbol-reference graph. "
                "It is the cleanest currently available approximation to a semantic architectural core."
            ),
            scope_note=(
                "This remains heuristic because symbol-reference detection is syntactic and does not run Lean elaboration."
            ),
            signal_edge_metadata=core_semantic_edge_metadata,
        ) if core_semantic_records else {
            "node_count": 0,
            "edge_count": 0,
            "sources": [],
            "sinks": [],
            "transitive_reduction": {"edge_count": 0, "edges": [], "sources": [], "sinks": []},
            "weighted_mainline": None,
            "mainline": {"length": 0, "path": [], "source": None, "sink": None, "groups": [], "edges": []},
        }

    clean_discipline_bridges = compute_clean_discipline_bridge_summary(discipline_overview, kept_modules, rec_by_module)
    open_namespaces_by_module = None if symbol_reference_export_context is None else symbol_reference_export_context.get("open_namespaces_by_module")
    declarations_by_module = None if symbol_reference_export_context is None else symbol_reference_export_context.get("declarations_by_module")
    raw_text_by_module = None if symbol_reference_export_context is None else symbol_reference_export_context.get("raw_text_by_module")
    mainline_mismatch_report = compute_mainline_mismatch_report(
        syntactic_signal_plan,
        semantic_signal_plan,
        core_semantic_edge_metadata,
        rec_by_module,
    )
    mainline_edge_forensics = compute_mainline_edge_forensics(
        syntactic_signal_plan,
        semantic_signal_plan,
        core_semantic_edge_metadata,
        rec_by_module,
        open_namespaces_by_module,
        declarations_by_module,
    )
    weak_mainline_edges = compute_weak_mainline_edges(mainline_edge_forensics)
    edge_case_reports = compute_edge_case_reports(
        mainline_edge_forensics,
        weak_mainline_edges,
        rec_by_module,
        symbol_reference_export_context,
    )
    sink_taxonomy = compute_sink_taxonomy(syntactic_signal_plan, rec_by_module)
    trunk_vs_extensions = compute_trunk_vs_extensions(
        core_records,
        core_semantic_adj if semantic_dependency_adj is not None else None,
        core_semantic_edge_metadata,
        syntactic_signal_plan,
        semantic_signal_plan,
        output_dir,
    )
    summary = {
        "artifact_module_count": int(artifact_info["artifact_module_count"]),
        "core_module_count": int(artifact_info["core_module_count"]),
        "artifact_reason_counts": artifact_info["artifact_reason_counts"],
        "files": {
            "artifact_modules": "architectural_core/artifact_modules.json",
            "syntactic_signal_plan": "architectural_core/syntactic_signal_plan/summary.json",
            "semantic_signal_plan": "architectural_core/semantic_signal_plan/summary.json" if semantic_signal_plan is not None else None,
            "clean_discipline_bridges": "architectural_core/clean_discipline_bridges.json" if clean_discipline_bridges is not None else None,
            "clean_bridge_rankings": "architectural_core/clean_bridge_rankings.json" if clean_discipline_bridges is not None else None,
            "mainline_mismatch_report": "architectural_core/mainline_mismatch_report.json" if mainline_mismatch_report is not None else None,
            "mainline_edge_forensics": "architectural_core/mainline_edge_forensics.json" if mainline_edge_forensics is not None else None,
            "weak_mainline_edges": "architectural_core/weak_mainline_edges.json" if weak_mainline_edges is not None else None,
            "missing_mainline_edge_forensics": "architectural_core/missing_mainline_edge_forensics.json" if edge_case_reports is not None and edge_case_reports["missing_report_count"] > 0 else None,
            "weak_edge_reports": "architectural_core/weak_edge_reports.json" if edge_case_reports is not None and edge_case_reports["weak_report_count"] > 0 else None,
            "edge_case_report_index": "architectural_core/edge_case_reports/index.json" if edge_case_reports is not None and edge_case_reports["report_count"] > 0 else None,
            "sink_taxonomy": "architectural_core/sink_taxonomy.json",
            "trunk_vs_extensions": "architectural_core/trunk_vs_extensions.json" if trunk_vs_extensions is not None else None,
            "robust_semantic_signal_plan": "architectural_core/robust_semantic_signal_plan/summary.json" if trunk_vs_extensions is not None else None,
        },
        "syntactic_signal_plan": {
            "node_count": syntactic_signal_plan["node_count"],
            "edge_count": syntactic_signal_plan["edge_count"],
            "source_count": len(syntactic_signal_plan["sources"]),
            "sink_count": len(syntactic_signal_plan["sinks"]),
            "reduced_edge_count": syntactic_signal_plan["transitive_reduction"]["edge_count"],
            "mainline_length": syntactic_signal_plan["mainline"]["length"],
            "mainline_source": syntactic_signal_plan["mainline"]["source"],
            "mainline_sink": syntactic_signal_plan["mainline"]["sink"],
        },
        "semantic_signal_plan": None if semantic_signal_plan is None else {
            "node_count": semantic_signal_plan["node_count"],
            "edge_count": semantic_signal_plan["edge_count"],
            "source_count": len(semantic_signal_plan["sources"]),
            "sink_count": len(semantic_signal_plan["sinks"]),
            "reduced_edge_count": semantic_signal_plan["transitive_reduction"]["edge_count"],
            "mainline_length": semantic_signal_plan["mainline"]["length"],
            "weighted_mainline_length": 0 if semantic_signal_plan.get("weighted_mainline") is None else semantic_signal_plan["weighted_mainline"]["length"],
            "weighted_mainline_score": 0.0 if semantic_signal_plan.get("weighted_mainline") is None else semantic_signal_plan["weighted_mainline"]["total_score"],
            "mainline_source": semantic_signal_plan["mainline"]["source"],
            "mainline_sink": semantic_signal_plan["mainline"]["sink"],
        },
        "clean_discipline_bridges": None if clean_discipline_bridges is None else {
            "bridge_count": clean_discipline_bridges["bridge_count"],
            "bridge_module_count": len(clean_discipline_bridges["bridge_modules"]),
            "top_bridge_modules": clean_discipline_bridges["bridge_modules"][:10],
            "top_bridge_edges": clean_discipline_bridges["bridge_rankings"]["bridge_edge_rankings"][:10],
        },
        "mainline_mismatch_report": None if mainline_mismatch_report is None else {
            "syntactic_mainline_length": mainline_mismatch_report["syntactic_mainline_length"],
            "semantic_mainline_length": mainline_mismatch_report["semantic_mainline_length"],
            "weighted_semantic_mainline_length": mainline_mismatch_report["weighted_semantic_mainline_length"],
            "shared_edge_count_with_semantic_mainline": mainline_mismatch_report["shared_edge_count_with_semantic_mainline"],
            "shared_edge_count_with_weighted_mainline": mainline_mismatch_report["shared_edge_count_with_weighted_mainline"],
            "syntactic_edges_missing_in_semantic_graph": mainline_mismatch_report["syntactic_edges_missing_in_semantic_graph"],
            "syntactic_edges_only_weakly_supported": mainline_mismatch_report["syntactic_edges_only_weakly_supported"],
        },
        "mainline_edge_forensics": None if mainline_edge_forensics is None else {
            "edge_count": mainline_edge_forensics["edge_count"],
            "status_counts": mainline_edge_forensics["status_counts"],
        },
        "weak_mainline_edges": None if weak_mainline_edges is None else {
            "edge_count": weak_mainline_edges["edge_count"],
        },
        "edge_case_reports": None if edge_case_reports is None else {
            "report_count": edge_case_reports["report_count"],
            "missing_report_count": edge_case_reports["missing_report_count"],
            "weak_report_count": edge_case_reports["weak_report_count"],
        },
        "sink_taxonomy": {
            "sink_count": sink_taxonomy["sink_count"],
            "classification_counts": sink_taxonomy["classification_counts"],
        },
        "trunk_vs_extensions": None if trunk_vs_extensions is None else {
            "minimum_confidence_weight": trunk_vs_extensions["minimum_confidence_weight"],
            "minimum_confidence_classes": trunk_vs_extensions["minimum_confidence_classes"],
            "robust_edge_count": trunk_vs_extensions["robust_edge_count"],
            "heuristic_edge_count": trunk_vs_extensions["heuristic_edge_count"],
            "robust_trunk": trunk_vs_extensions["robust_trunk"],
        },
    }

    write_json(core_dir / "artifact_modules.json", artifact_info)
    write_json(core_dir / "summary.json", summary)
    if clean_discipline_bridges is not None:
        write_json(core_dir / "clean_discipline_bridges.json", clean_discipline_bridges)
        write_json(core_dir / "clean_bridge_rankings.json", clean_discipline_bridges["bridge_rankings"])
    if mainline_mismatch_report is not None:
        write_json(core_dir / "mainline_mismatch_report.json", mainline_mismatch_report)
    if mainline_edge_forensics is not None:
        write_json(core_dir / "mainline_edge_forensics.json", mainline_edge_forensics)
    if weak_mainline_edges is not None:
        write_json(core_dir / "weak_mainline_edges.json", weak_mainline_edges)
    if edge_case_reports is not None:
        edge_case_dir = core_dir / "edge_case_reports"
        edge_case_dir.mkdir(parents=True, exist_ok=True)
        write_json(edge_case_dir / "index.json", edge_case_reports)
        if edge_case_reports["missing_report_count"] > 0:
            write_json(core_dir / "missing_mainline_edge_forensics.json", edge_case_reports["missing_reports"])
        if edge_case_reports["weak_report_count"] > 0:
            write_json(core_dir / "weak_edge_reports.json", edge_case_reports["weak_reports"])
        for idx, report in enumerate(edge_case_reports["reports"], start=1):
            prefix = "missing" if report["status"] == "missing" else "weak"
            write_json(edge_case_dir / f"{idx:02d}_{prefix}_{report['slug']}.json", report)
    write_json(core_dir / "sink_taxonomy.json", sink_taxonomy)
    if trunk_vs_extensions is not None:
        write_json(core_dir / "trunk_vs_extensions.json", trunk_vs_extensions)

    readme_lines = [
        "# Architectural core export",
        "",
        "This directory adds a cleaned architectural view on top of the raw import export.",
        "",
        f"- Artifact modules filtered: **{summary['artifact_module_count']}**",
        f"- Core modules retained: **{summary['core_module_count']}**",
        f"- Clean syntactic signal edges: **{summary['syntactic_signal_plan']['edge_count']}**",
        f"- Clean syntactic mainline length: **{summary['syntactic_signal_plan']['mainline_length']}**",
        f"- Clean semantic mainline length: **{summary['semantic_signal_plan']['mainline_length']}**" if summary["semantic_signal_plan"] is not None else "- Clean semantic mainline length: not computed",
        f"- Clean discipline bridges: **{summary['clean_discipline_bridges']['bridge_count']}**" if summary["clean_discipline_bridges"] is not None else "- Clean discipline bridges: not computed",
        f"- Weak clean-mainline edges: **{summary['weak_mainline_edges']['edge_count']}**" if summary["weak_mainline_edges"] is not None else "- Weak clean-mainline edges: not computed",
        f"- Edge-case reports: **{summary['edge_case_reports']['report_count']}**" if summary["edge_case_reports"] is not None else "- Edge-case reports: not computed",
        "",
        "## Artifact rules",
        "",
        "- `build_module`: file stem `BuildAll`",
        "- `notation_module`: file stem `Notation`",
        "- `top_level_umbrella`: top-level wrapper importing exactly one `*.BuildAll` module",
        "- `umbrella_module`: non-top-level wrapper importing exactly one `*.BuildAll` module and not consumed internally",
        "- `isolated_internal_module`: no internal imports and no internal importers",
        "",
        "The cleaned view is diagnostic only. It should be read alongside the raw export, not instead of it.",
        "",
    ]
    (core_dir / "README.md").write_text("\n".join(readme_lines), encoding="utf-8")
    return {
        "summary": summary,
        "artifact_modules": artifact_info,
        "syntactic_signal_plan": syntactic_signal_plan,
        "semantic_signal_plan": semantic_signal_plan,
        "clean_discipline_bridges": clean_discipline_bridges,
        "mainline_mismatch_report": mainline_mismatch_report,
        "mainline_edge_forensics": mainline_edge_forensics,
        "weak_mainline_edges": weak_mainline_edges,
        "edge_case_reports": edge_case_reports,
        "sink_taxonomy": sink_taxonomy,
        "trunk_vs_extensions": trunk_vs_extensions,
    }


def default_discipline_specs(internal_prefix: str) -> list[DisciplineSpec]:
    if internal_prefix != "CNNA":
        return []
    return [
        DisciplineSpec(
            name="prenumeric_toc_substrate_graph",
            description="Pre-numeric substrate, ToC, addressing, finite region/core and graph-facing foundations.",
            include_modules=[],
            include_prefixes=[
                "CNNA.PillarA.Foundation",
                "CNNA.PillarA.ToC",
                "CNNA.PillarA.Finite.CutSpec",
                "CNNA.PillarA.Finite.RegionCore",
                "CNNA.PillarA.Finite.BoundaryPorts",
                "CNNA.PillarA.Finite.Selection",
                "CNNA.PillarA.Finite.Approximant",
            ],
            include_regexes=[],
            exclude_modules=[],
            exclude_prefixes=[],
            exclude_regexes=[],
        ),
        DisciplineSpec(
            name="dirichlet_dtn_schur_network",
            description="Dirichlet, DtN, closure regularization, Schur coupling and network-facing transport.",
            include_modules=[],
            include_prefixes=[
                "CNNA.PillarA.Finite.DirichletLaplacian",
                "CNNA.PillarA.DtN",
                "CNNA.PillarA.Closure",
                "CNNA.PillarA.Coupling",
                "CNNA.PillarA.Network",
                "CNNA.PillarA.Sectors",
            ],
            include_regexes=[],
            exclude_modules=[],
            exclude_prefixes=[],
            exclude_regexes=[],
        ),
        DisciplineSpec(
            name="topology_algebra_cd_completion",
            description="Algebraic, geometric and Cayley-Dickson-completion-facing layer, including Handoff closure material.",
            include_modules=[],
            include_prefixes=[
                "CNNA.PillarA.Geometry",
                "CNNA.PillarA.Handoff.Core.Step1MathData",
                "CNNA.PillarA.Handoff.Core.Step1StrongCore",
                "CNNA.PillarA.Handoff.Core.SectorExport",
                "CNNA.PillarA.Handoff.Outputs.A_to_B",
                "CNNA.PillarA.Foundation.ExecComplex",
                "CNNA.PillarA.Foundation.ExecComplexLemmas",
                "CNNA.PillarA.Foundation.ExecComplexBridge",
                "CNNA.PillarA.Foundation.MatrixAlgebra",
                "CNNA.PillarA.Foundation.MatrixNorms",
                "CNNA.PillarA.Foundation.HermitianStructure",
                "CNNA.PillarA.Foundation.FiniteHilbert",
            ],
            include_regexes=[r"^CNNA\.Structural\.CayleyDickson\.S6"],
            exclude_modules=[],
            exclude_prefixes=[],
            exclude_regexes=[],
        ),
    ]


def load_discipline_specs(config_path: Path | None, internal_prefixes: tuple[str, ...]) -> tuple[list[DisciplineSpec], str]:
    if config_path is None:
        specs = default_discipline_specs(internal_prefixes[0])
        return specs, "default"
    payload = json.loads(config_path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict) or "disciplines" not in payload or not isinstance(payload["disciplines"], list):
        raise ExportError("discipline config must be a JSON object with a 'disciplines' list")
    specs: list[DisciplineSpec] = []
    for idx, raw in enumerate(payload["disciplines"], start=1):
        if not isinstance(raw, dict):
            raise ExportError(f"discipline entry {idx} is not an object")
        name = raw.get("name")
        if not isinstance(name, str) or not name.strip():
            raise ExportError(f"discipline entry {idx} must have a non-empty string field 'name'")
        spec = DisciplineSpec(
            name=name,
            description=str(raw.get("description", "")),
            include_modules=[str(x) for x in raw.get("include_modules", [])],
            include_prefixes=[str(x) for x in raw.get("include_prefixes", [])],
            include_regexes=[str(x) for x in raw.get("include_regexes", [])],
            exclude_modules=[str(x) for x in raw.get("exclude_modules", [])],
            exclude_prefixes=[str(x) for x in raw.get("exclude_prefixes", [])],
            exclude_regexes=[str(x) for x in raw.get("exclude_regexes", [])],
        )
        specs.append(spec)
    return specs, str(config_path)


def compile_discipline_specs(specs: list[DisciplineSpec]) -> list[DisciplineCompiled]:
    compiled: list[DisciplineCompiled] = []
    for spec in specs:
        compiled.append(
            DisciplineCompiled(
                spec=spec,
                include_patterns=[re.compile(p) for p in spec.include_regexes],
                exclude_patterns=[re.compile(p) for p in spec.exclude_regexes],
            )
        )
    return compiled


def module_matches_discipline(module: str, compiled: DisciplineCompiled) -> bool:
    spec = compiled.spec
    included = False
    if module in spec.include_modules:
        included = True
    if any(module == pref or module.startswith(pref + ".") for pref in spec.include_prefixes):
        included = True
    if any(p.search(module) for p in compiled.include_patterns):
        included = True
    if not included:
        return False
    if module in spec.exclude_modules:
        return False
    if any(module == pref or module.startswith(pref + ".") for pref in spec.exclude_prefixes):
        return False
    if any(p.search(module) for p in compiled.exclude_patterns):
        return False
    return True


def compute_discipline_exports(
    records: list[ModuleRecord],
    adjacency: dict[str, list[str]],
    compiled_specs: list[DisciplineCompiled],
    output_dir: Path,
) -> dict[str, object]:
    rec_by_module = {r.module: r for r in records}
    memberships: dict[str, list[str]] = defaultdict(list)
    discipline_modules: dict[str, list[str]] = {}

    for compiled in compiled_specs:
        modules = sorted(m for m in rec_by_module if module_matches_discipline(m, compiled))
        discipline_modules[compiled.spec.name] = modules
        for mod in modules:
            memberships[mod].append(compiled.spec.name)

    discipline_root = output_dir / "disciplines"
    discipline_root.mkdir(parents=True, exist_ok=True)

    bridge_pairs: dict[tuple[str, str], list[dict[str, object]]] = defaultdict(list)
    discipline_payloads: dict[str, dict[str, object]] = {}
    node_groups = {r.module: r.group for r in records}

    for compiled in compiled_specs:
        name = compiled.spec.name
        slug = slugify(name)
        modules = discipline_modules[name]
        module_set = set(modules)
        local_adj = {m: sorted(dst for dst in adjacency.get(m, []) if dst in module_set) for m in modules}
        reverse_local = reverse_edges(local_adj)
        entry_modules = sorted(m for m in modules if not reverse_local.get(m, []))
        terminal_modules = sorted(m for m in modules if not local_adj.get(m, []))
        topo, cycles = topo_sort_dependency_first(modules, local_adj)

        outgoing_bridges: list[dict[str, object]] = []
        incoming_bridges: list[dict[str, object]] = []
        for src in modules:
            for dst in adjacency.get(src, []):
                if dst in module_set:
                    continue
                target_disciplines = sorted(memberships.get(dst, []))
                edge = {
                    "source": src,
                    "target": dst,
                    "source_disciplines": sorted(memberships.get(src, [])),
                    "target_disciplines": target_disciplines,
                    "target_group": rec_by_module.get(dst).group if dst in rec_by_module else None,
                }
                outgoing_bridges.append(edge)
                for target_name in target_disciplines:
                    if target_name != name:
                        bridge_pairs[(name, target_name)].append(edge)
        for src, dsts in adjacency.items():
            if src in module_set:
                continue
            for dst in dsts:
                if dst in module_set:
                    source_disciplines = sorted(memberships.get(src, []))
                    incoming_bridges.append({
                        "source": src,
                        "target": dst,
                        "source_disciplines": source_disciplines,
                        "target_disciplines": sorted(memberships.get(dst, [])),
                        "source_group": rec_by_module[src].group if src in rec_by_module else None,
                    })

        payload = {
            "name": name,
            "slug": slug,
            "description": compiled.spec.description,
            "module_count": len(modules),
            "modules": modules,
            "entry_modules": entry_modules,
            "terminal_modules": terminal_modules,
            "internal_edge_count": sum(len(v) for v in local_adj.values()),
            "internal_edges": [
                {"source": src, "target": dst}
                for src in modules for dst in local_adj.get(src, [])
            ],
            "outgoing_bridge_count": len(outgoing_bridges),
            "incoming_bridge_count": len(incoming_bridges),
            "outgoing_bridges": sorted(outgoing_bridges, key=lambda x: (x["source"], x["target"])),
            "incoming_bridges": sorted(incoming_bridges, key=lambda x: (x["source"], x["target"])),
            "dependency_order": topo,
            "acyclic": not bool(cycles),
            "cycles": cycles,
            "spec": asdict(compiled.spec),
        }
        discipline_payloads[name] = payload

        subdir = discipline_root / slug
        subdir.mkdir(parents=True, exist_ok=True)
        write_json(subdir / "summary.json", payload)
        write_subgraph_dot(subdir / "graph.dot", f"discipline_{slug}", modules, local_adj, node_groups, payload["outgoing_bridges"] + payload["incoming_bridges"])
        md_lines = [
            f"# Discipline audit export: {name}",
            "",
            compiled.spec.description,
            "",
            f"- Modules: **{len(modules)}**",
            f"- Internal edges: **{payload['internal_edge_count']}**",
            f"- Outgoing bridges: **{len(outgoing_bridges)}**",
            f"- Incoming bridges: **{len(incoming_bridges)}**",
            f"- Acyclic: **{payload['acyclic']}**",
            "",
            "## Entry modules",
            "",
        ]
        md_lines.extend([f"- `{m}`" for m in entry_modules] or ["- none"])
        md_lines.extend(["", "## Terminal modules", ""])
        md_lines.extend([f"- `{m}`" for m in terminal_modules] or ["- none"])
        md_lines.extend(["", "## Modules", ""])
        md_lines.extend([f"- `{m}`" for m in modules] or ["- none"])
        md_lines.append("")
        (subdir / "README.md").write_text("\n".join(md_lines), encoding="utf-8")

    bridge_summary = []
    for (src_name, dst_name), edges in sorted(bridge_pairs.items()):
        bridge_summary.append({
            "source_discipline": src_name,
            "target_discipline": dst_name,
            "edge_count": len(edges),
            "edges": sorted(edges, key=lambda x: (x["source"], x["target"])),
        })

    unassigned = sorted(m for m in rec_by_module if not memberships.get(m))
    overlapping = {m: sorted(v) for m, v in memberships.items() if len(v) > 1}

    bridge_rankings = compute_bridge_rankings(bridge_summary, rec_by_module)

    overview = {
        "discipline_count": len(compiled_specs),
        "disciplines": discipline_payloads,
        "module_memberships": {k: sorted(v) for k, v in sorted(memberships.items())},
        "unassigned_modules": unassigned,
        "overlapping_memberships": overlapping,
        "bridges": bridge_summary,
        "bridge_rankings": bridge_rankings,
    }
    write_json(discipline_root / "summary.json", overview)
    write_json(discipline_root / "bridge_summary.json", bridge_summary)
    write_json(discipline_root / "bridge_rankings.json", bridge_rankings)
    write_json(discipline_root / "top_bridge_modules.json", bridge_rankings["bridge_module_rankings"])
    write_json(discipline_root / "top_bridge_edges.json", bridge_rankings["bridge_edge_rankings"])

    lines = ["# Discipline audit export", ""]
    for compiled in compiled_specs:
        payload = discipline_payloads[compiled.spec.name]
        lines.extend([
            f"## {compiled.spec.name}",
            "",
            compiled.spec.description,
            "",
            f"- Modules: **{payload['module_count']}**",
            f"- Internal edges: **{payload['internal_edge_count']}**",
            f"- Outgoing bridges: **{payload['outgoing_bridge_count']}**",
            f"- Incoming bridges: **{payload['incoming_bridge_count']}**",
            f"- Acyclic: **{payload['acyclic']}**",
            f"- Files: `disciplines/{payload['slug']}/summary.json`, `disciplines/{payload['slug']}/graph.dot`",
            "",
        ])
    if unassigned:
        lines.append("## Unassigned modules")
        lines.append("")
        for mod in unassigned:
            lines.append(f"- `{mod}`")
        lines.append("")
    if bridge_summary:
        lines.append("## Discipline bridges")
        lines.append("")
        for item in bridge_summary:
            lines.append(f"- `{item['source_discipline']}` → `{item['target_discipline']}`: {item['edge_count']} edge(s)")
        lines.append("")
        lines.append("## Ranked bridge files")
        lines.append("")
        lines.append("- `bridge_rankings.json`")
        lines.append("- `top_bridge_modules.json`")
        lines.append("- `top_bridge_edges.json`")
        lines.append("")
    (discipline_root / "README.md").write_text("\n".join(lines), encoding="utf-8")
    return overview


def build_validation_warnings(module_count: int, internal_edge_count: int, external_edge_count: int, missing_internal_edge_count: int, modules: list[str], internal_prefixes: tuple[str, ...], source_root_arg: str) -> list[str]:
    warnings: list[str] = []
    if module_count > 1000:
        warnings.append("Very large module count; you may have scanned a repo root that includes .lake/packages or other external trees.")
    if internal_edge_count == 0 and missing_internal_edge_count > 0:
        warnings.append("No internal edges were found even though imports with internal prefixes exist; repo_root/source_root is probably misaligned with module names.")
    if source_root_arg in {".", "./"}:
        warnings.append("source_root is '.', which often creates prefixed module names that no longer match imports; prefer --source-root CNNA for this project. With the planning tool defaults this resolves to Repository/repo_snapshot/CNNA.")
    foreign_named = [m for m in modules if not any(m == p or m.startswith(p + ".") for p in internal_prefixes)]
    if module_count and len(foreign_named) > max(20, module_count // 4):
        warnings.append("Many discovered modules lie outside the declared internal prefixes; this usually indicates an overly broad source root.")
    if external_edge_count > 0 and internal_edge_count == 0 and module_count > 0:
        warnings.append("All edges are external; this is usually not a real project graph but a mis-scoped scan.")
    return warnings


def write_default_discipline_config(path: Path, internal_prefixes: tuple[str, ...]) -> None:
    payload = {"disciplines": [asdict(spec) for spec in default_discipline_specs(internal_prefixes[0])]}
    write_json(path, payload)


def main() -> int:
    script_path = Path(__file__).resolve()
    default_repo_root = find_default_repo_root(script_path)
    parser = argparse.ArgumentParser(description="Export exact Lean module and direct import lists/graphs from .lean source files.")
    parser.add_argument("repo_root", nargs="?", default=str(default_repo_root), help="Lean repo root containing the source root. Default: Repository/repo_snapshot.")
    parser.add_argument("--source-root", default="CNNA", help="Lean source root relative to repo_root. Default: CNNA, so the default source tree is Repository/repo_snapshot/CNNA.")
    parser.add_argument("--output-dir", default=None, help="Output directory. Default: Repository/repo_inventory/raw_export")
    parser.add_argument("--internal-prefix", action="append", dest="internal_prefixes", default=None, help="Internal module prefix. Can be repeated. Default: first path component of source root.")
    parser.add_argument("--group-depth", type=int, default=2, help="Path depth after source root for group summaries. Default: 2")
    parser.add_argument("--hotspot-count", type=int, default=20, help="How many hotspot rows to emit per ranking. Default: 20")
    parser.add_argument("--discipline-config", default=None, help="Optional JSON config for discipline audit exports.")
    parser.add_argument("--write-default-discipline-config", default=None, help="Write the built-in default discipline config JSON to this path and continue.")
    parser.add_argument("--skip-signal-plan", action="store_true", help="Do not generate the forward signal-plan export.")
    parser.add_argument("--skip-symbol-references", action="store_true", help="Do not generate the heuristic symbol-reference export.")
    args = parser.parse_args()

    repo_root = Path(args.repo_root).resolve()
    source_root = (repo_root / args.source_root).resolve()
    if not source_root.exists():
        print(f"error: source root does not exist: {source_root}", file=sys.stderr)
        return 2

    default_prefix = Path(args.source_root).parts[0] if Path(args.source_root).parts else args.source_root
    internal_prefixes = tuple(sorted(set(args.internal_prefixes or [default_prefix])))
    output_dir = Path(args.output_dir).resolve() if args.output_dir else find_default_output_dir(script_path)
    output_dir.mkdir(parents=True, exist_ok=True)

    if args.write_default_discipline_config:
        write_default_discipline_config(Path(args.write_default_discipline_config).resolve(), internal_prefixes)

    module_to_path, module_meta = collect_modules(repo_root, source_root)
    internal_modules = set(module_to_path)

    raw_imports: dict[str, list[str]] = {}
    internal_adj: dict[str, list[str]] = {}
    external_by_module: dict[str, list[str]] = {}
    missing_by_module: dict[str, list[str]] = {}
    prelude_by_module: dict[str, bool] = {}

    for module, path in sorted(module_to_path.items()):
        saw_prelude, imports = parse_imports(path)
        prelude_by_module[module] = saw_prelude
        raw_imports[module] = imports
        internal, external, missing = classify_imports(imports, internal_modules, internal_prefixes)
        internal_adj[module] = internal
        external_by_module[module] = external
        missing_by_module[module] = missing

    reverse_internal = reverse_edges(internal_adj)
    reverse_all: dict[str, set[str]] = defaultdict(set)
    for src, imports in raw_imports.items():
        for dst in imports:
            reverse_all[dst].add(src)
    reverse_all_sorted = {k: sorted(v) for k, v in reverse_all.items()}

    records: list[ModuleRecord] = []
    nodes = sorted(module_to_path)
    for module in nodes:
        imports = raw_imports[module]
        internal_imports = internal_adj[module]
        internal_imported_by = reverse_internal.get(module, [])
        imported_by = reverse_all_sorted.get(module, [])
        path_after_source_root = list(module_meta[module]["path_after_source_root"])
        records.append(ModuleRecord(
            module=module,
            path=str(module_meta[module]["relative_path"]),
            imports=imports,
            internal_imports=internal_imports,
            external_imports=external_by_module[module],
            missing_internal_imports=missing_by_module[module],
            imported_by=imported_by,
            internal_imported_by=internal_imported_by,
            external_imported_by=sorted(set(imported_by) - set(internal_imported_by)),
            transitive_internal_imports=transitive_closure(module, internal_adj),
            prelude=prelude_by_module[module],
            is_build_module=bool(module_meta[module]["is_build_module"]),
            is_notation_module=bool(module_meta[module]["is_notation_module"]),
            group=pick_group(path_after_source_root, args.group_depth),
            path_after_source_root=path_after_source_root,
        ))

    topo_order, cycles = topo_sort_dependency_first(nodes, internal_adj)

    module_payload = {
        "repo_root": str(repo_root),
        "source_root": str(source_root),
        "source_root_argument": args.source_root,
        "internal_prefixes": list(internal_prefixes),
        "modules": [asdict(r) for r in records],
    }
    internal_edges = [{"source": src, "target": dst} for src in nodes for dst in internal_adj.get(src, [])]
    external_edges = [{"source": src, "target": dst} for src in nodes for dst in external_by_module.get(src, [])]
    missing_internal_edges = [{"source": src, "target": dst} for src in nodes for dst in missing_by_module.get(src, [])]
    edges_payload = {
        "internal_edges": internal_edges,
        "external_edges": external_edges,
        "missing_internal_edges": missing_internal_edges,
    }
    warnings = build_validation_warnings(len(nodes), len(internal_edges), len(external_edges), len(missing_internal_edges), nodes, internal_prefixes, args.source_root)
    stats_payload = {
        "module_count": len(nodes),
        "internal_edge_count": len(internal_edges),
        "external_edge_count": len(external_edges),
        "missing_internal_edge_count": len(missing_internal_edges),
        "acyclic": not bool(cycles),
        "cycles": cycles,
        "dependency_order": topo_order,
        "validation_warnings": warnings,
    }

    signal_plan = None if args.skip_signal_plan else compute_signal_plan(records, internal_adj, output_dir)
    if signal_plan is not None:
        stats_payload["signal_plan"] = {
            "source_count": len(signal_plan["sources"]),
            "sink_count": len(signal_plan["sinks"]),
            "signal_edge_count": signal_plan["edge_count"],
            "reduced_signal_edge_count": signal_plan["transitive_reduction"]["edge_count"],
            "mainline_length": signal_plan["mainline"]["length"],
            "mainline_source": signal_plan["mainline"]["source"],
            "mainline_sink": signal_plan["mainline"]["sink"],
        }

    symbol_reference_export = None if args.skip_symbol_references else compute_symbol_reference_export(records, module_to_path, internal_adj, output_dir)
    if symbol_reference_export is not None:
        symbol_summary = symbol_reference_export["summary"]
        stats_payload["symbol_references"] = {
            "declaration_count": symbol_summary["declaration_count"],
            "reference_edge_count": symbol_summary["reference_edge_count"],
            "referenced_symbol_count": symbol_summary["referenced_symbol_count"],
            "consumer_module_count": symbol_summary["consumer_module_count"],
            "referenced_dependency_module_count": symbol_summary["referenced_dependency_module_count"],
            "confidence_counts": symbol_summary["confidence_counts"],
            "semantic_signal_plan": symbol_summary["semantic_signal_plan"],
            "modules_with_open_namespaces": symbol_summary.get("modules_with_open_namespaces", 0),
            "opened_namespace_count": symbol_summary.get("opened_namespace_count", 0),
        }

    write_json(output_dir / "modules.json", module_payload)
    write_json(output_dir / "import_edges.json", edges_payload)
    write_json(output_dir / "signal_plan_summary.json", signal_plan if signal_plan is not None else {})
    write_json(output_dir / "symbol_reference_summary.json", symbol_reference_export["summary"] if symbol_reference_export is not None else {})
    write_csv(
        output_dir / "modules.csv",
        [
            "module", "group", "path", "imports_count", "internal_imports_count", "external_imports_count",
            "missing_internal_imports_count", "internal_imported_by_count", "transitive_internal_imports_count",
            "is_build_module", "is_notation_module", "prelude",
        ],
        [
            [
                r.module, r.group, r.path, len(r.imports), len(r.internal_imports), len(r.external_imports),
                len(r.missing_internal_imports), len(r.internal_imported_by), len(r.transitive_internal_imports),
                int(r.is_build_module), int(r.is_notation_module), int(r.prelude),
            ]
            for r in records
        ],
    )
    write_csv(
        output_dir / "import_edges.csv",
        ["source", "target", "kind"],
        [[e["source"], e["target"], "internal"] for e in internal_edges]
        + [[e["source"], e["target"], "external"] for e in external_edges]
        + [[e["source"], e["target"], "missing_internal"] for e in missing_internal_edges],
    )
    write_dot(output_dir / "import_graph.dot", nodes, module_to_path, internal_adj, raw_imports, internal_prefixes)
    write_json(output_dir / "dependency_order.json", {"dependency_order": topo_order, "acyclic": not bool(cycles), "cycles": cycles})
    (output_dir / "dependency_order.txt").write_text("\n".join(topo_order) + ("\n" if topo_order else ""), encoding="utf-8")

    group_summary = compute_group_summary(records, internal_adj)
    write_json(output_dir / "group_summary.json", group_summary)
    group_subgraphs = output_dir / "group_subgraphs"
    group_subgraphs.mkdir(parents=True, exist_ok=True)
    rec_by_module = {r.module: r for r in records}
    for group, payload in group_summary["groups"].items():
        modules = payload["modules"]
        module_set = set(modules)
        local_adj = {m: sorted(dst for dst in internal_adj.get(m, []) if dst in module_set) for m in modules}
        write_subgraph_dot(group_subgraphs / f"{slugify(group)}.dot", f"group_{slugify(group)}", modules, local_adj, {m: rec_by_module[m].group for m in modules})

    hotspots = compute_hotspots(records, args.hotspot_count)
    write_json(output_dir / "hotspots.json", hotspots)

    config_path = Path(args.discipline_config).resolve() if args.discipline_config else None
    specs, config_origin = load_discipline_specs(config_path, internal_prefixes)
    discipline_overview = {"config_origin": config_origin, "discipline_count": 0, "disciplines": {}, "module_memberships": {}, "unassigned_modules": [], "overlapping_memberships": {}, "bridges": []}
    if specs:
        discipline_overview = compute_discipline_exports(records, internal_adj, compile_discipline_specs(specs), output_dir)
        discipline_overview["config_origin"] = config_origin
        write_json(output_dir / "discipline_summary.json", discipline_overview)
    else:
        write_json(output_dir / "discipline_summary.json", discipline_overview)

    architectural_core_export = compute_architectural_core_export(
        records,
        internal_adj,
        output_dir,
        semantic_dependency_adj=None if symbol_reference_export is None else symbol_reference_export["semantic_dependency_adj"],
        semantic_signal_edge_metadata=None if symbol_reference_export is None else symbol_reference_export["semantic_signal_edge_metadata"],
        symbol_reference_export_context=symbol_reference_export,
        discipline_overview=discipline_overview,
    )
    stats_payload["architectural_core"] = architectural_core_export["summary"]
    write_json(output_dir / "architectural_core_summary.json", architectural_core_export["summary"])
    write_json(output_dir / "stats.json", stats_payload)
    write_markdown_summary(output_dir / "README.md", repo_root, source_root, records, topo_order, cycles, internal_prefixes, warnings, signal_plan, symbol_reference_export, architectural_core_export)

    print(f"wrote export to: {output_dir}")
    print(f"modules: {len(nodes)}")
    print(f"internal edges: {len(internal_edges)}")
    print(f"external edges: {len(external_edges)}")
    if missing_internal_edges:
        print(f"missing internal edges: {len(missing_internal_edges)}")
    if cycles:
        print(f"cycles detected: {len(cycles)}")
    else:
        print("graph is acyclic")
    if signal_plan is not None:
        print(f"signal sources: {len(signal_plan['sources'])}")
        print(f"signal sinks: {len(signal_plan['sinks'])}")
        print(f"reduced signal edges: {signal_plan['transitive_reduction']['edge_count']}")
        print(f"mainline length: {signal_plan['mainline']['length']}")
    if symbol_reference_export is not None:
        symbol_summary = symbol_reference_export["summary"]
        print(f"symbol declarations: {symbol_summary['declaration_count']}")
        print(f"symbol reference edges: {symbol_summary['reference_edge_count']}")
        print(f"semantic signal edges: {symbol_summary['semantic_signal_plan']['edge_count']}")
        print(f"semantic mainline length: {symbol_summary['semantic_signal_plan']['mainline_length']}")
        if symbol_summary['semantic_signal_plan'].get('weighted_mainline_length'):
            print(f"weighted semantic mainline length: {symbol_summary['semantic_signal_plan']['weighted_mainline_length']}")
    if warnings:
        print(f"validation warnings: {len(warnings)}")
    if specs:
        print(f"disciplines: {len(specs)}")
        print(f"discipline bridges: {len(discipline_overview.get('bridges', []))}")
    core_summary = architectural_core_export["summary"]
    print(f"artifact modules: {core_summary['artifact_module_count']}")
    print(f"core modules: {core_summary['core_module_count']}")
    print(f"clean signal sources: {core_summary['syntactic_signal_plan']['source_count']}")
    print(f"clean signal sinks: {core_summary['syntactic_signal_plan']['sink_count']}")
    print(f"clean mainline length: {core_summary['syntactic_signal_plan']['mainline_length']}")
    if core_summary["semantic_signal_plan"] is not None:
        print(f"clean semantic mainline length: {core_summary['semantic_signal_plan']['mainline_length']}")
        if core_summary["semantic_signal_plan"].get("weighted_mainline_length"):
            print(f"clean weighted semantic mainline length: {core_summary['semantic_signal_plan']['weighted_mainline_length']}")
    if core_summary.get("mainline_mismatch_report") is not None:
        print(f"clean mainline semantic mismatches: {core_summary['mainline_mismatch_report']['syntactic_edges_missing_in_semantic_graph']}")
    if core_summary.get("weak_mainline_edges") is not None:
        print(f"clean weak mainline edges: {core_summary['weak_mainline_edges']['edge_count']}")
    if core_summary.get("edge_case_reports") is not None:
        print(f"clean edge case reports: {core_summary['edge_case_reports']['report_count']}")
        print(f"clean missing edge reports: {core_summary['edge_case_reports']['missing_report_count']}")
        print(f"clean weak edge reports: {core_summary['edge_case_reports']['weak_report_count']}")
    if core_summary.get("sink_taxonomy") is not None:
        print(f"clean ambiguous sinks: {core_summary['sink_taxonomy']['classification_counts'].get('ambiguous_leaf', 0)}")
    if core_summary.get("trunk_vs_extensions") is not None:
        print(f"clean robust semantic edges: {core_summary['trunk_vs_extensions']['robust_edge_count']}")
        print(f"clean heuristic semantic edges: {core_summary['trunk_vs_extensions']['heuristic_edge_count']}")
    if core_summary["clean_discipline_bridges"] is not None:
        print(f"clean discipline bridges: {core_summary['clean_discipline_bridges']['bridge_count']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
