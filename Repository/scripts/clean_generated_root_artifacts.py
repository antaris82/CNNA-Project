#!/usr/bin/env python3
"""Clean generated documentation artifacts from the Repository root.

The package-root Lean/Lake build-entry files live one level above Repository/
and are not touched by this script.

Policy:
- Do not keep an active README.md in Repository root; the maintained README lives only in the package root.
- If Lean/Lake project-control files are ever present here, preserve them defensively; the canonical copy lives in the package root.
- Move root Markdown reports, including accidental Repository/README.md copies, to archive/reports/.
- Delete root PDF/TeX/LaTeX build artifacts by default when --apply is used.
- Never touch source/control directories such as masters, scripts, repo_snapshot,
  repo_inventory, tables, generated_exports, context_docs, or figures.
"""
from __future__ import annotations

import argparse
import json
import shutil
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPORT_ARCHIVE = ROOT / "archive" / "reports"
EXPORTS = ROOT / "generated_exports"

DELETE_SUFFIXES = {
    ".pdf", ".tex", ".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk", ".synctex.gz"
}
KEEP_ROOT_FILES = {"CNNA.lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain"}


def classify(path: Path) -> str:
    name = path.name
    if name in KEEP_ROOT_FILES:
        return "keep"
    if path.suffix == ".md":
        return "archive-md-report"
    for suffix in sorted(DELETE_SUFFIXES, key=len, reverse=True):
        if name.endswith(suffix):
            return "delete-generated-doc-artifact"
    return "ignore"


def main() -> None:
    ap = argparse.ArgumentParser(description="Archive Markdown reports and remove disposable generated docs from Repository root while preserving Lean/Lake project-control files. The maintained README lives only in the package root.")
    ap.add_argument("--apply", action="store_true", help="Actually move/delete files. Without this, only reports planned actions.")
    ap.add_argument("--archive-generated", action="store_true", help="Move PDF/TeX/build artifacts to archive/generated_root_artifacts instead of deleting them.")
    args = ap.parse_args()

    actions: list[dict[str, str]] = []
    generated_archive = ROOT / "archive" / "generated_root_artifacts"
    for path in sorted(p for p in ROOT.iterdir() if p.is_file()):
        action = classify(path)
        if action == "keep" or action == "ignore":
            continue
        rec = {"file": path.name, "action": action}
        if action == "archive-md-report":
            target = REPORT_ARCHIVE / path.name
            rec["target"] = str(target.relative_to(ROOT))
            if args.apply:
                REPORT_ARCHIVE.mkdir(parents=True, exist_ok=True)
                if target.exists():
                    target.unlink()
                shutil.move(str(path), str(target))
        elif action == "delete-generated-doc-artifact":
            if args.archive_generated:
                target = generated_archive / path.name
                rec["action"] = "archive-generated-doc-artifact"
                rec["target"] = str(target.relative_to(ROOT))
                if args.apply:
                    generated_archive.mkdir(parents=True, exist_ok=True)
                    if target.exists():
                        target.unlink()
                    shutil.move(str(path), str(target))
            elif args.apply:
                path.unlink()
        actions.append(rec)

    summary = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "root": str(ROOT),
        "applied": bool(args.apply),
        "archive_generated": bool(args.archive_generated),
        "actions": actions,
        "counts": {},
    }
    for rec in actions:
        summary["counts"][rec["action"]] = summary["counts"].get(rec["action"], 0) + 1
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    if args.apply:
        EXPORTS.mkdir(exist_ok=True)
        (EXPORTS / "root_artifact_cleanup.generated.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
