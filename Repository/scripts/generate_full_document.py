#!/usr/bin/env python3
"""Generate the full CNNA planning document outside the repository root.

The Single-YAML-Master and generated tables remain the maintained sources.
This script creates disposable full-document TeX/PDF outputs under
Repository/generated_docs/full/ so versioned PDFs/TeX files no longer need to
accumulate in the project root.
"""
from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path
from typing import Any

import yaml

ROOT = Path(__file__).resolve().parents[1]
MASTER = ROOT / "masters" / "cnna_roadmap_master.yaml"
OUT_DIR = ROOT / "generated_docs" / "full"


def _load_metadata() -> dict[str, Any]:
    data = yaml.safe_load(MASTER.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or not isinstance(data.get("metadata"), dict):
        raise SystemExit("masters/cnna_roadmap_master.yaml has no metadata mapping")
    return data["metadata"]


def _safe_filename_part(value: str) -> str:
    value = value.replace(":", "-").replace("+", "plus")
    value = re.sub(r"[^A-Za-z0-9_.-]+", "_", value)
    return value.strip("_") or "unknown"


def _meta(metadata: dict[str, Any], key: str, fallback: str = "unknown") -> str:
    aliases = {
        "tool_infrastructure_version": ("tool_infrastructure_version", "tool_version"),
        "tool_infrastructure_timestamp": ("tool_infrastructure_timestamp", "tool_change_timestamp"),
        "planning_data_version": ("planning_data_version",),
        "planning_data_timestamp": ("planning_data_timestamp",),
        "lean_data_timestamp": ("lean_data_timestamp", "data_timestamp"),
        "lean_data_version": ("lean_data_version", "data_version"),
    }
    for candidate in aliases.get(key, (key,)):
        value = metadata.get(candidate)
        if value not in (None, ""):
            return str(value)
    return fallback


def _tex(metadata: dict[str, Any]) -> str:
    tool_version = _meta(metadata, "tool_infrastructure_version")
    tool_timestamp = _meta(metadata, "tool_infrastructure_timestamp")
    planning_version = _meta(metadata, "planning_data_version")
    planning_timestamp = _meta(metadata, "planning_data_timestamp")
    lean_version = _meta(metadata, "lean_data_version")
    data_timestamp = _meta(metadata, "lean_data_timestamp")
    date = str(metadata.get("date", ""))
    editor = str(metadata.get("editor", "Jan Seeck (antaris)"))
    assistant = str(metadata.get("assistant", "ChatGPT (OpenAI)"))
    minimum_requirement = str(metadata.get("minimum_assistant_requirement", "ChatGPT Plus account with GPT-5.5 for the tested ChatGPT-instantiated workflow"))
    title_version = tool_version.replace("_", r"\_")
    title_tool_timestamp = tool_timestamp.replace("_", r"\_").replace("+", r"+")
    title_planning_version = planning_version.replace("_", r"\_")
    title_planning_timestamp = planning_timestamp.replace("_", r"\_").replace("+", r"+")
    title_lean_version = lean_version.replace("_", r"\_")
    title_timestamp = data_timestamp.replace("_", r"\_").replace("+", r"+")
    title_editor = editor.replace("_", r"\_")
    title_assistant = assistant.replace("_", r"\_")
    title_requirement = minimum_requirement.replace("_", r"\_")
    return rf"""\documentclass[11pt,a3paper,landscape]{{article}}
\usepackage[utf8]{{inputenc}}
\usepackage[T1]{{fontenc}}
\usepackage[english]{{babel}}
\usepackage{{lmodern}}
\usepackage{{amsmath,amssymb,mathtools}}
\usepackage[a3paper,margin=8mm,landscape]{{geometry}}
\usepackage{{array,longtable,booktabs,tabularx}}
\usepackage{{graphicx}}
\usepackage[table]{{xcolor}}
\definecolor{{orange}}{{RGB}}{{255,165,0}}
\usepackage{{enumitem}}
\usepackage{{hyperref}}
\usepackage{{bookmark}}
\usepackage{{etoolbox}}
\hypersetup{{colorlinks=true,linkcolor=blue,urlcolor=blue,linktoc=all,bookmarks=true,bookmarksnumbered=true,bookmarksopen=false}}
\bookmarksetup{{numbered,open=false}}
\setcounter{{tocdepth}}{{1}}
\pretocmd{{\section}}{{\clearpage}}{{}}{{}}
\setlist[itemize]{{leftmargin=*,itemsep=0.08em,topsep=0.16em}}
\newcolumntype{{L}}[1]{{>{{\raggedright\arraybackslash}}p{{#1}}}}
\renewcommand{{\arraystretch}}{{1.18}}
\setlength{{\tabcolsep}}{{3.0pt}}
\setlength{{\extrarowheight}}{{1.1pt}}
\emergencystretch=10em
\title{{CNNA Planning and Documentation Tool\\[0.3em]Tool infra {title_version} @ {title_tool_timestamp}\\[0.2em]Planning data {title_planning_version} @ {title_planning_timestamp}\\[0.2em]Lean toolchain {title_lean_version}; Lean data @ {title_timestamp}}}
\author{{Editor: {title_editor}\\Assistant: {title_assistant}\\{{\normalsize Minimum tested assistant setup: {title_requirement}}}}}
\date{{{date}}}
\begin{{document}}
\maketitle
\pdfbookmark[1]{{Contents}}{{toc}}
\tableofcontents
\clearpage


\section{{Stats}}
\paragraph{{What this section shows.}} This opening section is a generated-secondary orientation surface. It collects project-scale facts, credit and license metadata, the tool-interface metaphor, and the repository module inventory generated from the frozen Lean snapshot. It is shown first so a reader can see the scope, version, graph conventions and review boundary before reading planning tables.
\input{{tables/stats.tex}}

\section{{Latest change overview}}
\paragraph{{What this section shows.}} This table combines fixed metadata from the Master YAML with the latest manually recorded tool/display changes. It explains what changed in this package version and, equally important, whether the Lean toolchain version or Lean-code data timestamp changed. It is displayed to prevent generated documentation changes from being mistaken for Lean-source changes.
\input{{tables/latest_change_overview.tex}}

\section{{Working format and module mapping}}
\paragraph{{What this section shows.}} This section records the maintained work format, root/source layout, and module-mapping assumptions. Its source is the Single-YAML-Master. It is shown because file placement, generated-output handling and source-root conventions affect every later command and review packet.
\input{{tables/format_decision.tex}}

\section{{Static code findings}}
\paragraph{{What this section shows.}} This table lists static findings discovered during repository review, implementation rehearsals and tool maintenance. Each row has a lifecycle status, addressing phase and version/timestamp. It is shown to keep known risks, closed issues and unresolved structural problems explicit rather than leaving them in chat history.
\input{{tables/code_audit.tex}}

\section{{Global no-go guardrails}}
\paragraph{{What this section shows.}} This table contains global rules that every phase inherits. The data comes from the Master YAML, not from Lean. It is shown because these rules constrain how new phases, refactors, generated documents and Lean implementation prompts may proceed.
\input{{tables/global_no_go_guardrails.tex}}

\section{{Global ontic postulates}}
\paragraph{{What this section shows.}} This section records the global ontic/provenance postulates used by the planning layer. It is intentionally separated from Lean axioms: these statements guide the roadmap and review discipline, but do not become Lean theorems by appearing here.
\input{{tables/global_postulates.tex}}

\section{{Phase-object-link policy}}
\paragraph{{What this section shows.}} This policy explains how phases and objects are linked in the generated documentation. The table is shown before the object and phase registers so the reader knows when a linked object is directly owned by a phase and when it is only part of an umbrella scope.
\input{{tables/phase_object_link_policy.tex}}

\section{{Phase/object context-class taxonomy}}
\paragraph{{What this section shows.}} This section adds an object-oriented class layer above phases and objects. Status colors say release/proof state; context class says what kind of row it is: Lean, tool, database mirror, generated artifact, documentation, governance, or external reference gate. It is shown before object and phase registers to prevent tool-only or reference-only rows from being read as Lean objects.
\input{{tables/context_class_taxonomy.tex}}

\section{{Object/phase significance and documentation-depth tiers}}
\paragraph{{What this section shows.}} This section adds a second orthogonal classification axis: not what a row is, but how fundamental it is and how much proof/documentation burden it carries. It prevents fundamental generator or handoff objects from being under-documented while keeping trivial, auxiliary, or mention-only rows from bloating the proofbook.
\input{{tables/object_significance_taxonomy.tex}}

\section{{Lean declaration total-classification taxonomy}}
\paragraph{{What this section shows.}} This table defines the vocabulary required for complete Lean declaration classification. It is stricter than the consumption-classification map: every Lean declaration must be assigned a syntactic kind, semantic role, triviality tier, documentation requirement, lifecycle state, public-surface status and owner/non-object bucket before the source-intake and Explorer-readiness gates can close.
\input{{tables/lean_declaration_classification_taxonomy.tex}}

\section{{External source and legacy-roadmap cross-check}}
\paragraph{{What this section shows.}} This section tracks external review prompts, uploaded legacy-roadmap obligations and mathematical warnings. It is comparison, migration and correction context only. It is shown to keep established-theory and legacy-roadmap cautions visible without importing them as CNNA generators.
\input{{tables/external_source_crosscheck.tex}}

\section{{Secondary long-term goals}}
\paragraph{{What this section shows.}} This table contains side objectives and long-horizon tool/theory ambitions, including database and interactive-map directions. The rows are shown because some principles apply immediately even if their technical realization remains later. They must not displace the active Lean/content path.
\input{{tables/secondary_long_term_goals.tex}}

\section{{Standardized phase-preparation, implementation, and documentation workflows}}
\paragraph{{What this section shows.}} This section describes repeatable workflows over the Master YAML state: how to rehearse implementability, close a phase, prepare context documentation, add workflows or route missing structures back to their natural origin. It is shown because the main value of the tool is workflow scalability, not merely static tables.
\input{{tables/workflow_policy.tex}}
\input{{tables/pre_implementation_phase_check_policy.tex}}
\input{{tables/pre_implementation_phase_check_results.tex}}

\section{{Implementation-scaling phase plan}}
\paragraph{{What this section shows.}} This table records how the planning/documentation tool itself may grow without taking over the mathematical implementation. It distinguishes Python tooling, generated views, future database paths and review infrastructure from Lean-derived CNNA objects.
\input{{tables/implementation_scaling_phase_plan.tex}}

\section{{Reuse/duplication ledger and canonical generator policy}}
\paragraph{{What this section shows.}} This ledger tracks reuse seams, duplicated implementation risks, generator boundaries and canonical-source decisions. It is shown because compactness and reuse are allowed only where provenance and reviewability improve; duplicate generator paths or consumer-side patches are blocked by default.
\input{{tables/reuse_duplication_ledger.tex}}

\section{{Declaration consumption classification map}}
\paragraph{{What this section shows.}} This section summarizes generated declaration-consumption classification. It separates semantic consumption from mere import reachability and exports the full records as TSV. The PDF renders summaries so reviewers can see the API/firewall shape without reading an unreadable declaration dump.
\input{{tables/consumption_classification_map.tex}}

\section{{Canonical object register with code derivation sites}}
\paragraph{{What this section shows.}} This register is the canonical object/quantity index maintained in the Master YAML. It shows object status, derivation/provenance text, code locations, access rights, handoff rights and proof-dossier links. It is shown before the phase table so phase release can be checked against registered objects.
\input{{tables/object_register.tex}}

\section{{Object and quantities proof documentation}}
\paragraph{{What this section shows.}} This generated proofbook section gives one dossier row per registered object or quantity. A dossier is not automatically a Lean proof: it states source objects, definitions, proof targets, proof sketches and verification status. It is shown so expert review can inspect each object without reading the entire repository.
\input{{tables/object_proof_documentation.tex}}

\section{{Phase table in natural derivation order}}
\paragraph{{What this section shows.}} This is the primary roadmap table. It is the authoritative generated view for phase status, dependencies, linked objects, current code sites, target modules/objects, proof goals and implementation scratchpad links. Lean-derivation phases are red by default until released by derived-only object evidence; yellow is the unique active phase; orange is implementable after stated predecessor closure; white is reserved for non-direct-Lean tooling, infrastructure, documentation, comparison or refactor work.
\input{{tables/phase_table.tex}}

\section{{Implementation scratch pad}}
\paragraph{{What this section shows.}} This section records how each phase was prepared, implemented or closed. It is the detailed audit trail behind the phase table: changed files, proof strategy, expected tactics, build status, no-go checks, dependency audit and post-implementation notes. It is shown after the phase table because it explains the evidence behind phase-state changes.
\input{{tables/implementation_scratchpad.tex}}

\section{{Technical appendix: module-change manifest and semantic placement gate}}
\paragraph{{What this section shows.}} This appendix is not a second phase table. It is a narrow module-change ledger used only when a phase proposes new Lean modules, module moves, module merges, public API changes or import-surface changes. Ordinary planning, documentation and tool phases should be governed by the main phase table plus scratchpad instead. The appendix is kept for auditability of real code-surface changes, not for normal roadmap reading.
\input{{tables/module_implementation_manifest.tex}}

\end{{document}}
"""


def main() -> None:
    ap = argparse.ArgumentParser(description="Generate disposable full CNNA documentation outside the project root.")
    ap.add_argument("--compile", action="store_true", help="Run pdflatex twice after writing TeX.")
    ap.add_argument("--out-dir", default=str(OUT_DIR), help="Output directory, default: Repository/generated_docs/full")
    args = ap.parse_args()

    metadata = _load_metadata()
    out_dir = Path(args.out_dir)
    if not out_dir.is_absolute():
        out_dir = ROOT / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    tool_version = _safe_filename_part(_meta(metadata, "tool_infrastructure_version"))
    tool_timestamp = _safe_filename_part(_meta(metadata, "tool_infrastructure_timestamp"))
    planning_version = _safe_filename_part(_meta(metadata, "planning_data_version"))
    planning_timestamp = _safe_filename_part(_meta(metadata, "planning_data_timestamp"))
    lean_version = _safe_filename_part(_meta(metadata, "lean_data_version", _meta(metadata, "lean_data_timestamp")))
    lean_timestamp = _safe_filename_part(_meta(metadata, "lean_data_timestamp"))
    stem = f"CNNA_Planning_ToolInfra_{tool_version}_{tool_timestamp}_Planning_{planning_version}_{planning_timestamp}_Lean_{lean_version}_{lean_timestamp}_A3_English"
    tex_path = out_dir / f"{stem}.tex"
    tex_path.write_text(_tex(metadata), encoding="utf-8")
    print(f"Wrote {tex_path.relative_to(ROOT)}")

    if args.compile:
        for _ in range(2):
            subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "-output-directory", str(out_dir), str(tex_path)],
                cwd=ROOT,
                check=True,
            )
        print(f"Compiled {tex_path.with_suffix('.pdf').relative_to(ROOT)}")


if __name__ == "__main__":
    main()
