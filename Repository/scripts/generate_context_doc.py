#!/usr/bin/env python3
"""Generate a context-filtered CNNA documentation packet.

This script is intentionally a generated-secondary view over the existing
Single-YAML-Master and generated TSV exports. It does not create CNNA truth,
does not modify Lean code, and does not certify semantic correctness.
"""

import argparse
import csv
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, List, Sequence, Tuple

try:
    import yaml
except ImportError as exc:  # pragma: no cover
    raise SystemExit("PyYAML is required: pip install pyyaml") from exc

ROOT = Path(__file__).resolve().parents[1]
MASTER_FILE = ROOT / "masters" / "cnna_roadmap_master.yaml"
EXPORT_DIR = ROOT / "generated_exports"
CONTEXT_ROOT = ROOT / "context_docs"

SECTION_ORDER: List[Tuple[str, str, str]] = [
    ("project_stats", "Stats: project facts and repository module inventory", "export-prefix"),
    ("latest_change_overview", "Latest change overview", "master"),
    ("format_decision", "Working format and module mapping", "master"),
    ("code_audit", "Static code findings", "master"),
    ("global_no_go_guardrails", "Global no-go guardrails", "master"),
    ("global_postulates", "Global ontic postulates", "master"),
    ("phase_object_link_policy", "Phase-object-link policy", "master"),
    ("external_source_crosscheck", "TomS thread source cross-check", "master"),
    ("secondary_long_term_goals", "Secondary long-term goals", "master"),
    ("workflow_policy", "Standardized phase-preparation, implementation, and documentation workflows", "master"),
    ("pre_implementation_phase_check_policy", "Pre-implementation phase-check policy", "master"),
    ("pre_implementation_phase_check_results", "Current pre-implementation phase-window check", "master"),
    ("implementation_scaling_phase_plan", "Implementation-scaling phase plan", "master"),
    ("reuse_duplication_ledger", "Reuse/duplication ledger and canonical generator policy", "master"),
    ("consumption_classification_map", "Declaration consumption classification map", "export-prefix"),
    ("object_register", "Canonical object register with code derivation sites", "master:objects"),
    ("object_proof_documentation", "Object and quantities proof documentation", "master:object_proof_dossiers"),
    ("phase_roadmap", "Phase table in natural derivation order", "master:phases"),
    ("implementation_scratchpad", "Implementation scratch pad", "master"),
    ("module_implementation_manifest", "Technical appendix: module-change manifest and semantic placement gate", "export"),
]


SECTION_EXPLANATIONS: Dict[str, str] = {
    "project_stats": "Orientation data generated from metadata, repository inventory and registered planning rows. It explains scope, credits, license context and graph conventions before the detailed plan starts.",
    "latest_change_overview": "Three-layer version/change metadata from the Master YAML. It separates Lean-code data state, YAML planning/register state, and tool-infrastructure code state.",
    "format_decision": "Maintained source-layout and working-format rules from the Master YAML. It explains which files are source/control and which outputs are disposable views.",
    "code_audit": "Static findings from code/tool review. It keeps known risks, closed issues and addressing phases explicit.",
    "global_no_go_guardrails": "Global workflow invariants inherited by phases and scratchpads. They constrain implementation, refactor and documentation work.",
    "global_postulates": "Roadmap-level ontic/provenance statements. They are not Lean axioms and do not become proof merely by appearing here.",
    "phase_object_link_policy": "Rules for interpreting phase-to-object links. It prevents umbrella scopes and direct object ownership from being confused.",
    "external_source_crosscheck": "External review/source cross-check material. It supplies comparison warnings and proof obligations, not CNNA-generative inputs.",
    "secondary_long_term_goals": "Long-horizon tool and theory objectives. Some governance principles apply now even when implementation is deferred.",
    "workflow_policy": "Repeatable workflows over the Master YAML state. This is where the tool's scalable value is recorded.",
    "pre_implementation_phase_check_policy": "Rules for forward implementation rehearsals before code is written.",
    "pre_implementation_phase_check_results": "Current implementability-window results. It records why a phase is yellow, orange, red, white or green.",
    "implementation_scaling_phase_plan": "How the planning/documentation tool may scale without becoming a CNNA truth source.",
    "reuse_duplication_ledger": "Reuse, duplicate-path and generator-boundary decisions. It blocks ad-hoc parallel paths unless a natural source seam is recorded.",
    "consumption_classification_map": "Generated declaration/object consumption classifications. It separates semantic consumption from mere import reachability.",
    "object_register": "Canonical object/quantity register from the Master YAML, including provenance, code sites, access and handoff rights.",
    "object_proof_documentation": "Proof-dossier records for each object/quantity. They package definitions, proof targets and review status for expert checking.",
    "phase_roadmap": "Primary phase table in natural derivation order. It owns status, dependencies, linked objects, code sites and proof goals.",
    "implementation_scratchpad": "Detailed per-phase implementation/preparation audit records behind the phase table.",
    "module_implementation_manifest": "Technical appendix only: a module-change ledger for new modules, moves, merges, public API or import-surface changes. It is not a second phase table.",
}

DEFAULT_DROP_TOKENS = {
    "the", "and", "or", "for", "with", "from", "into", "about", "zur", "zum", "der", "die", "das", "und", "oder",
    "eine", "einer", "eines", "doku", "dokumentation", "erstelle", "create", "documentation", "doc", "docs",
    "matrix",  # too broad in this project; profiles may use it only as a secondary scoring term
}

UNICODE_TEX_REPLACEMENTS = {
    "→": " -> ",
    "←": " <- ",
    "↔": " <-> ",
    "⇒": " => ",
    "⇐": " <= ",
    "⇔": " <=> ",
    "≤": " <= ",
    "≥": " >= ",
    "≠": " != ",
    "∈": " in ",
    "∉": " notin ",
    "∅": "empty-set",
    "Ω": "Omega",
    "ω": "omega",
    "β": "beta",
    "Δ": "Delta",
    "φ": "phi",
    "τ": "tau",
    "ρ": "rho",
    "ℝ": "R",
    "ℂ": "C",
    "ℕ": "N",
    "∗": "*",
    "∞": "infty",
    "–": "-",
    "—": "-",
    "‑": "-",
    "“": """,
    "”": """,
    "‘": "'",
    "’": "'",
}

@dataclass
class ContextProfile:
    profile_id: str
    title: str
    primary_terms: List[str]
    secondary_terms: List[str]
    excluded_terms: List[str]
    review_note: str


def load_master() -> Dict[str, Any]:
    if not MASTER_FILE.exists():
        raise SystemExit(f"missing master file: {MASTER_FILE}")
    data = yaml.safe_load(MASTER_FILE.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise SystemExit("master file must contain a YAML mapping")
    return data


def slugify(text: str) -> str:
    s = re.sub(r"[^a-zA-Z0-9]+", "_", text.strip().lower()).strip("_")
    return s or "context"


def tokenize(text: str) -> List[str]:
    return [t.lower() for t in re.findall(r"[A-Za-z0-9]+", text or "")]


def normalize_rows(section: Any) -> List[Dict[str, str]]:
    if section is None:
        return []
    if isinstance(section, dict):
        return [{str(k): value_to_text(v) for k, v in section.items()}]
    if not isinstance(section, list):
        return [{"value": value_to_text(section)}]
    rows: List[Dict[str, str]] = []
    for item in section:
        if isinstance(item, dict):
            rows.append({str(k): value_to_text(v) for k, v in item.items()})
        else:
            rows.append({"value": value_to_text(item)})
    return rows


def value_to_text(v: Any) -> str:
    if v is None:
        return ""
    if isinstance(v, (list, tuple)):
        return "; ".join(value_to_text(x) for x in v)
    if isinstance(v, dict):
        return json.dumps(v, ensure_ascii=False, sort_keys=True)
    return str(v)


def read_tsv(path: Path) -> List[Dict[str, str]]:
    if not path.exists():
        return []
    with path.open("r", encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f, delimiter="\t"))


def get_profiles(data: Dict[str, Any]) -> List[ContextProfile]:
    raw = data.get("context_documentation_profiles", []) or []
    profiles: List[ContextProfile] = []
    if not isinstance(raw, list):
        return profiles
    for rec in raw:
        if not isinstance(rec, dict):
            continue
        pid = str(rec.get("id", "")).strip()
        if not pid:
            continue
        profiles.append(ContextProfile(
            profile_id=pid,
            title=str(rec.get("title", pid)).strip(),
            primary_terms=[str(x) for x in rec.get("primary_terms", []) or []],
            secondary_terms=[str(x) for x in rec.get("secondary_terms", []) or []],
            excluded_terms=[str(x) for x in rec.get("excluded_terms", []) or []],
            review_note=str(rec.get("review_note", "")).strip(),
        ))
    return profiles


def choose_profile(query: str, explicit: str | None, profiles: Sequence[ContextProfile]) -> ContextProfile | None:
    if explicit:
        for p in profiles:
            if p.profile_id == explicit:
                return p
        raise SystemExit(f"unknown context profile {explicit!r}; available: {', '.join(p.profile_id for p in profiles)}")
    q = query.lower()
    q_slug = slugify(query).replace("_", "-")
    for p in profiles:
        if p.profile_id.lower() in {q, q_slug}:
            return p
    for p in profiles:
        profile_terms = [p.profile_id.lower(), p.title.lower()] + [t.lower() for t in p.primary_terms]
        if any(term and term in q for term in profile_terms):
            return p
    return None


def terms_for_query(query: str, profile: ContextProfile | None) -> Tuple[List[str], List[str], List[str]]:
    if profile:
        primary = [t.lower() for t in profile.primary_terms if str(t).strip()]
        secondary = [t.lower() for t in profile.secondary_terms if str(t).strip()]
        excluded = [t.lower() for t in profile.excluded_terms if str(t).strip()]
        return primary, secondary, excluded
    toks = [t for t in tokenize(query) if t not in DEFAULT_DROP_TOKENS and len(t) >= 2]
    return toks, [], []


def row_text(row: Dict[str, str]) -> str:
    return "\n".join(f"{k}: {v}" for k, v in row.items())


def score_row(row: Dict[str, str], primary: Sequence[str], secondary: Sequence[str], excluded: Sequence[str]) -> Tuple[int, List[str]]:
    text = row_text(row).lower()
    if any(term and term in text for term in excluded):
        return 0, []
    hits: List[str] = []
    primary_hits: List[str] = []
    score = 0
    for term in primary:
        if term and term in text:
            primary_hits.append(term)
            hits.append(term)
            score += 5
    # Curated profiles use secondary terms only for ranking after a primary-profile hit.
    # This prevents broad words like matrix, operator, boundary, or interface from selecting unrelated rows.
    if secondary and not primary_hits:
        return 0, []
    for term in secondary:
        if term and term in text:
            hits.append(term)
            score += 1
    return score, hits


def collect_section_rows(data: Dict[str, Any], section_id: str, source: str) -> List[Dict[str, str]]:
    if source == "master":
        return normalize_rows(data.get(section_id, []))
    if source.startswith("master:"):
        return normalize_rows(data.get(source.split(":", 1)[1], []))
    if source == "export":
        return read_tsv(EXPORT_DIR / f"{section_id}.generated.tsv")
    if source == "export-prefix":
        rows: List[Dict[str, str]] = []
        for p in sorted(EXPORT_DIR.glob(f"{section_id}*.generated.tsv")):
            for row in read_tsv(p):
                enriched = {"Generated export": p.name}
                enriched.update(row)
                rows.append(enriched)
        if section_id in {"module_inventory", "project_stats"}:
            # Also include related module/declaration exports if present.
            related = ["module_implementation_manifest.generated.tsv", "module_consumption_records.generated.tsv", "declaration_consumption_records.generated.tsv"]
            if section_id == "project_stats":
                related = ["project_stats.generated.tsv", "guiding_metaphors.generated.tsv", "license_notice.generated.tsv"] + related
            for name in related:
                for row in read_tsv(EXPORT_DIR / name):
                    enriched = {"Generated export": name}
                    enriched.update(row)
                    rows.append(enriched)
        if section_id == "consumption_classification_map":
            for name in ["consumption_classification_map.generated.tsv", "module_consumption_records.generated.tsv", "declaration_consumption_records.generated.tsv", "object_consumption_classification.generated.tsv"]:
                for row in read_tsv(EXPORT_DIR / name):
                    enriched = {"Generated export": name}
                    enriched.update(row)
                    rows.append(enriched)
        return rows
    return []


def tex_escape(s: Any) -> str:
    text = value_to_text(s)
    for src, dst in UNICODE_TEX_REPLACEMENTS.items():
        text = text.replace(src, dst)
    out: List[str] = []
    for ch in text:
        if ch == "&": out.append(r"\&")
        elif ch == "%": out.append(r"\%")
        elif ch == "$": out.append(r"\$")
        elif ch == "#": out.append(r"\#")
        elif ch == "_": out.append(r"\_")
        elif ch == "{": out.append(r"\{")
        elif ch == "}": out.append(r"\}")
        elif ch == "~": out.append(r"\textasciitilde{}")
        elif ch == "^": out.append(r"\textasciicircum{}")
        elif ch == "\\": out.append(r"\textbackslash{}")
        elif ch == "\n": out.append(r"\newline ")
        else: out.append(ch)
    return "".join(out).replace("; ", r";\newline ")



def safe_filename(text: str) -> str:
    return slugify(text).replace("_generated_tsv", "")[:120] or "section"


def write_matched_row_exports(out_dir: Path, selected: List[Tuple[str, str, List[Tuple[Dict[str, str], int, List[str]]], int]]) -> None:
    rows_dir = out_dir / "matched_rows"
    rows_dir.mkdir(exist_ok=True)
    for sec_id, _sec_title, entries, _total in selected:
        if not entries:
            continue
        keys: List[str] = ["context_score", "matched_terms"]
        for row, _score, _hits in entries:
            for k in row.keys():
                if k not in keys:
                    keys.append(k)
        with (rows_dir / f"{safe_filename(sec_id)}.matched.tsv").open("w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, delimiter="\t", fieldnames=keys)
            writer.writeheader()
            for row, score, hits in entries:
                out = {"context_score": str(score), "matched_terms": "; ".join(hits)}
                out.update(row)
                writer.writerow(out)

def write_context_tex(out_tex: Path, *, query: str, slug: str, profile: ContextProfile | None,
                      primary: Sequence[str], secondary: Sequence[str], manifest: Dict[str, Any],
                      selected: List[Tuple[str, str, List[Tuple[Dict[str, str], int, List[str]]], int]],
                      pdf_max_rows_per_section: int | None) -> None:
    title = f"CNNA context documentation slice: {query}"
    metadata = manifest.get("metadata", {}) if isinstance(manifest.get("metadata", {}), dict) else {}
    editor_tex = tex_escape(str(metadata.get("editor", "Jan Seeck (antaris)")))
    assistant_tex = tex_escape(str(metadata.get("assistant", "ChatGPT (OpenAI)")))
    requirement_tex = tex_escape(str(metadata.get("minimum_assistant_requirement", "ChatGPT Plus account with GPT-5.5 for the tested ChatGPT-instantiated workflow")))
    lines: List[str] = []
    lines.extend([
        r"\documentclass[11pt,a3paper,landscape]{article}",
        r"\usepackage[utf8]{inputenc}",
        r"\usepackage[T1]{fontenc}",
        r"\usepackage[english]{babel}",
        r"\usepackage{lmodern}",
        r"\usepackage{amsmath,amssymb,mathtools}",
        r"\usepackage[a3paper,margin=8mm,landscape]{geometry}",
        r"\usepackage{array,longtable,booktabs}",
        r"\usepackage[table]{xcolor}",
        r"\usepackage{enumitem}",
        r"\usepackage{hyperref}",
        r"\usepackage{etoolbox}",
        r"\hypersetup{colorlinks=true,linkcolor=blue,urlcolor=blue,linktoc=all}",
        r"\newcolumntype{L}[1]{>{\raggedright\arraybackslash}p{#1}}",
        r"\renewcommand{\arraystretch}{1.15}",
        r"\setlength{\tabcolsep}{3pt}",
        r"\emergencystretch=10em",
        r"\pretocmd{\section}{\clearpage}{}{}",
        rf"\title{{{tex_escape(title)}\\[0.3em]\normalsize Generated-secondary filtered view}}",
        rf"\author{{Editor: {editor_tex}\\Assistant: {assistant_tex}\\{{\normalsize Minimum tested assistant setup: {requirement_tex}}}}}",
        rf"\date{{{tex_escape(datetime.now(timezone.utc).isoformat())}}}",
        r"\begin{document}",
        r"\maketitle",
        r"\tableofcontents",
        r"\section*{Context-slice warning}",
        r"\addcontentsline{toc}{section}{Context-slice warning}",
        r"This document is a context-filtered generated-secondary view over the Single-YAML-Master and generated TSV exports. It is not a CNNA truth source. Lean code remains the primary formal source, and even green Lean builds and generated artifacts require discipline-specific expert review for semantic correctness.",
        r"\section*{Filter manifest}",
        r"\addcontentsline{toc}{section}{Filter manifest}",
        r"\begin{longtable}{L{0.20\linewidth} L{0.76\linewidth}}",
        r"\hline",
        r"\textbf{Field} & \textbf{Value}\\",
        r"\hline",
        rf"Query & {tex_escape(query)}\\\hline",
        rf"Slug & {tex_escape(slug)}\\\hline",
        rf"Profile & {tex_escape(profile.profile_id if profile else 'auto-token-filter')}\\\hline",
        rf"Primary terms & {tex_escape('; '.join(primary) or 'none')}\\\hline",
        rf"Secondary terms & {tex_escape('; '.join(secondary) or 'none')}\\\hline",
        rf"PDF row cap per section & {tex_escape('none/full PDF' if pdf_max_rows_per_section is None else str(pdf_max_rows_per_section))}\\\hline",
        rf"Full matched-row exports & {tex_escape('context_docs/' + slug + '/matched_rows/*.matched.tsv')}\\\hline",
        rf"Review note & {tex_escape(profile.review_note if profile else 'No curated profile selected; token matching only.')}\\\hline",
        r"\end{longtable}",
    ])
    lines.append(r"\section{Section hit summary}")
    lines.append(r"\begin{longtable}{L{0.34\linewidth} L{0.12\linewidth} L{0.12\linewidth} L{0.36\linewidth}}")
    lines.append(r"\hline")
    lines.append(r"\textbf{Section} & \textbf{Matched} & \textbf{Total} & \textbf{Source}\\")
    lines.append(r"\hline")
    for sec_id, sec_title, entries, total in selected:
        source_kind = manifest["sections"][sec_id]["source"]
        lines.append(f"{tex_escape(sec_title)} & {len(entries)} & {total} & {tex_escape(source_kind)}\\\\")
        lines.append(r"\hline")
    lines.append(r"\end{longtable}")

    for sec_id, sec_title, entries, total in selected:
        lines.append(rf"\section{{{tex_escape(sec_title)}}}")
        explanation = SECTION_EXPLANATIONS.get(sec_id, "Generated-secondary rows selected from the Master YAML or generated TSV exports for this section.")
        lines.append(rf"\paragraph{{Purpose and source.}} {tex_escape(explanation)}")
        lines.append(rf"\paragraph{{Context rows.}} Matched {len(entries)} of {total} available rows for this section.")
        if not entries:
            lines.append(r"\paragraph{No context-specific entries.} The section is intentionally retained to preserve the full documentation topology, but no row matched the current filter profile.")
            continue
        render_entries = entries if pdf_max_rows_per_section is None else entries[:pdf_max_rows_per_section]
        if pdf_max_rows_per_section is not None and len(entries) > pdf_max_rows_per_section:
            lines.append(rf"\paragraph{{PDF compaction note.}} Showing the first {pdf_max_rows_per_section} rows by relevance score in the PDF. The full matched row set for this section is exported in \texttt{{matched\_rows/{tex_escape(safe_filename(sec_id))}.matched.tsv}}.")
        for idx, (row, score, hits) in enumerate(render_entries, start=1):
            row_id = row.get("ID") or row.get("Phase") or row.get("Object") or row.get("Workflow") or row.get("Generated export") or str(idx)
            lines.append(rf"\subsection*{{{tex_escape(str(idx) + '. ' + str(row_id))}}}")
            lines.append(r"\begin{longtable}{L{0.20\linewidth} L{0.76\linewidth}}")
            lines.append(r"\hline")
            lines.append(r"\textbf{Field} & \textbf{Value}\\")
            lines.append(r"\hline")
            lines.append(rf"Context score & {score}\\\hline")
            lines.append(rf"Matched terms & {tex_escape('; '.join(hits))}\\\hline")
            for k, v in row.items():
                if str(v).strip():
                    lines.append(rf"{tex_escape(k)} & {tex_escape(v)}\\")
                    lines.append(r"\hline\addlinespace[0.18em]")
            lines.append(r"\end{longtable}")
    lines.append(r"\end{document}")
    out_tex.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_manifest(out_dir: Path, manifest: Dict[str, Any]) -> None:
    (out_dir / "context_filter_manifest.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False), encoding="utf-8")
    with (out_dir / "context_section_summary.tsv").open("w", encoding="utf-8", newline="") as f:
        fieldnames = ["section_id", "section_title", "source", "matched_rows", "total_rows"]
        writer = csv.DictWriter(f, delimiter="\t", fieldnames=fieldnames)
        writer.writeheader()
        for sec_id, rec in manifest["sections"].items():
            writer.writerow({"section_id": sec_id, **rec})


def compile_pdf(tex_path: Path) -> bool:
    try:
        proc = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", tex_path.name],
            cwd=tex_path.parent,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=180,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired) as exc:
        (tex_path.with_suffix(".compile.log")).write_text(str(exc), encoding="utf-8")
        return False
    (tex_path.with_suffix(".compile.log")).write_text(proc.stdout, encoding="utf-8")
    return proc.returncode == 0


def generate_context_doc(query: str, *, slug: str | None = None, profile_id: str | None = None, compile_tex: bool = True, pdf_max_rows_per_section: int | None = 80) -> Path:
    data = load_master()
    profiles = get_profiles(data)
    profile = choose_profile(query, profile_id, profiles)
    primary, secondary, excluded = terms_for_query(query, profile)
    if not primary and not secondary:
        raise SystemExit("context filter has no usable terms; provide a more specific query or --profile")
    slug = slug or (profile.profile_id if profile else slugify(query))
    slug = slugify(slug)
    out_dir = CONTEXT_ROOT / slug
    out_dir.mkdir(parents=True, exist_ok=True)

    selected: List[Tuple[str, str, List[Tuple[Dict[str, str], int, List[str]]], int]] = []
    manifest: Dict[str, Any] = {
        "query": query,
        "slug": slug,
        "profile": profile.profile_id if profile else None,
        "profile_title": profile.title if profile else None,
        "primary_terms": list(primary),
        "secondary_terms": list(secondary),
        "excluded_terms": list(excluded),
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "master_file": str(MASTER_FILE.relative_to(ROOT)),
        "metadata": data.get("metadata", {}) if isinstance(data.get("metadata", {}), dict) else {},
        "truth_status": "generated-secondary; Lean code remains primary; expert review required",
        "pdf_max_rows_per_section": None,
        "sections": {},
    }
    for sec_id, title, source in SECTION_ORDER:
        rows = collect_section_rows(data, sec_id, source)
        matches: List[Tuple[Dict[str, str], int, List[str]]] = []
        for row in rows:
            score, hits = score_row(row, primary, secondary, excluded)
            if score > 0:
                matches.append((row, score, hits))
        matches.sort(key=lambda x: (-x[1], row_text(x[0])[:100]))
        selected.append((sec_id, title, matches, len(rows)))
        manifest["sections"][sec_id] = {
            "section_title": title,
            "source": source,
            "matched_rows": len(matches),
            "total_rows": len(rows),
        }
    manifest["pdf_max_rows_per_section"] = pdf_max_rows_per_section
    write_manifest(out_dir, manifest)
    write_matched_row_exports(out_dir, selected)
    tex_path = out_dir / f"{slug}_context_documentation.tex"
    write_context_tex(tex_path, query=query, slug=slug, profile=profile, primary=primary, secondary=secondary, manifest=manifest, selected=selected, pdf_max_rows_per_section=pdf_max_rows_per_section)
    if compile_tex:
        ok = compile_pdf(tex_path)
        if not ok:
            print(f"warning: PDF compilation failed; see {tex_path.with_suffix('.compile.log')}", file=sys.stderr)
    return out_dir


def main(argv: Sequence[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description="Generate a context-filtered CNNA documentation slice from the Single-YAML-Master and generated exports.")
    ap.add_argument("query", help="Natural-language context query, e.g. 'DtN Matrix'.")
    ap.add_argument("--profile", help="Optional curated profile id from context_documentation_profiles.")
    ap.add_argument("--slug", help="Output slug under Repository/context_docs/.")
    ap.add_argument("--no-pdf", action="store_true", help="Write TeX/JSON/TSV only; skip pdflatex.")
    ap.add_argument("--pdf-max-rows-per-section", type=int, default=80, help="Maximum rows rendered in the human PDF per section; full matched rows are always exported as TSV. Default: 80.")
    ap.add_argument("--full-pdf", action="store_true", help="Render every matched row into the PDF. This may create very large PDFs and slow pdflatex runs.")
    ns = ap.parse_args(argv)
    max_rows = None if ns.full_pdf else ns.pdf_max_rows_per_section
    out_dir = generate_context_doc(ns.query, slug=ns.slug, profile_id=ns.profile, compile_tex=not ns.no_pdf, pdf_max_rows_per_section=max_rows)
    print(f"Context documentation written to {out_dir.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
