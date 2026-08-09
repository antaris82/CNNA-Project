#!/usr/bin/env python3
"""Build the current CNNA main paper and supplementary PDF.

The build normalizes the document date and rebuilds the supplementary source
and PDF against the exact SHA-256 digest of the newly built main paper on every
run. XeLaTeX PDF object identifiers are not asserted to be byte-reproducible.
"""
from __future__ import annotations

from datetime import datetime, timezone
from pathlib import Path
import hashlib
import os
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
MAIN_TEX = ROOT / "derivation/paper/main/paper.tex"
MAIN_PDF = ROOT / "derivation/paper/main/paper.pdf"
SUPP_DIR = ROOT / "derivation/supplement"
SUPP_MD = SUPP_DIR / "supplementary.md"
SUPP_BODY = SUPP_DIR / "supplementary_body.tex"
SUPP_TEX = SUPP_DIR / "supplementary.tex"
SUPP_PDF = SUPP_DIR / "supplementary.pdf"
METADATA = ROOT / "derivation/paper/layout/CNNA_DOCUMENT_METADATA.tex"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def metadata_value(command: str) -> str:
    text = METADATA.read_text(encoding="utf-8")
    match = re.search(rf"\\newcommand\{{\\{re.escape(command)}\}}\{{([^}}]+)\}}", text)
    if not match:
        raise RuntimeError(f"metadata command not found: {command}")
    return match.group(1)


def build_env() -> dict[str, str]:
    date_iso = metadata_value("CNNADocumentDateISO")
    epoch = int(datetime.fromisoformat(date_iso).replace(tzinfo=timezone.utc).timestamp())
    env = os.environ.copy()
    env.update(
        {
            "SOURCE_DATE_EPOCH": str(epoch),
            "FORCE_SOURCE_DATE": "1",
            "TZ": "UTC",
        }
    )
    return env


def run(command: list[str], *, cwd: Path, env: dict[str, str]) -> None:
    subprocess.run(command, cwd=cwd, env=env, check=True)


def latex_build(
    source: Path,
    target: Path,
    *,
    env: dict[str, str],
    use_biber: bool = False,
) -> None:
    """Build in an isolated directory with an explicit XeLaTeX/Biber pipeline.

    `latexmk` can misclassify biblatex output as a BibTeX job when the build
    directory is external to the source tree.  The explicit pipeline avoids
    that ambiguity and keeps all intermediates outside the deliverable tree.
    """
    with tempfile.TemporaryDirectory(prefix="cnna_latex_") as tmp:
        out = Path(tmp)
        xelatex = [
            "xelatex",
            "-interaction=nonstopmode",
            "-halt-on-error",
            f"-output-directory={out}",
            str(source.relative_to(ROOT)),
        ]
        run(xelatex, cwd=ROOT, env=env)
        if use_biber:
            run(
                [
                    "biber",
                    "--input-directory",
                    str(out),
                    "--output-directory",
                    str(out),
                    source.stem,
                ],
                cwd=ROOT,
                env=env,
            )
        run(xelatex, cwd=ROOT, env=env)
        run(xelatex, cwd=ROOT, env=env)
        built = out / f"{source.stem}.pdf"
        if not built.exists():
            raise RuntimeError(f"expected PDF was not built: {built}")
        shutil.copy2(built, target)


def update_supplement_binding(main_hash: str) -> None:
    date_human = metadata_value("CNNADocumentDate")
    editor = metadata_value("CNNAEditor")
    (SUPP_DIR / "MAIN_PAPER_SHA256.txt").write_text(
        f"{main_hash}  derivation/paper/main/paper.pdf\n", encoding="utf-8"
    )
    (SUPP_DIR / "MAIN_PAPER_SHA256.tex").write_text(
        "% Hash of the exact current main-paper PDF.\n"
        f"\\newcommand{{\\CNNAMainPaperSHA}}{{{main_hash}}}\n",
        encoding="utf-8",
    )
    text = SUPP_MD.read_text(encoding="utf-8")
    text = re.sub(
        r"\A# From Primitive Provenance to Mathematical Structure — Supplementary Material\s*\n"
        r"(?:<!-- CNNA-DOCUMENT-METADATA-BEGIN -->.*?"
        r"<!-- CNNA-DOCUMENT-METADATA-END -->\s*\n)?",
        "# From Primitive Provenance to Mathematical Structure — Supplementary Material\n\n",
        text,
        flags=re.S,
    )
    metadata = (
        "<!-- CNNA-DOCUMENT-METADATA-BEGIN -->\n"
        "**Document status:** DRAFT  \n"
        f"**Current date:** {date_human}  \n"
        f"**Editor:** {editor}  \n"
        "**Bound main-paper PDF:** `derivation/paper/main/paper.pdf`  \n"
        f"**Main-paper SHA-256:** `{main_hash}`\n"
        "<!-- CNNA-DOCUMENT-METADATA-END -->\n\n"
    )
    SUPP_MD.write_text(
        text.replace(
            "# From Primitive Provenance to Mathematical Structure — Supplementary Material\n\n",
            "# From Primitive Provenance to Mathematical Structure — Supplementary Material\n\n" + metadata,
            1,
        ),
        encoding="utf-8",
    )


def wrap_texttt_with_seqsplit(tex: str) -> str:
    output: list[str] = []
    index = 0
    marker = r"\texttt{"
    while True:
        start_marker = tex.find(marker, index)
        if start_marker < 0:
            output.append(tex[index:])
            break
        output.append(tex[index:start_marker])
        start = start_marker + len(marker)
        depth = 1
        cursor = start
        while cursor < len(tex) and depth:
            char = tex[cursor]
            escaped = cursor > 0 and tex[cursor - 1] == "\\"
            if char == "{" and not escaped:
                depth += 1
            elif char == "}" and not escaped:
                depth -= 1
            cursor += 1
        if depth:
            raise RuntimeError("unbalanced texttt group in Pandoc output")
        content = tex[start : cursor - 1]
        output.append(r"\texttt{\protect\seqsplit{" + content + "}}")
        index = cursor
    return "".join(output)


def build_supplement_body(*, env: dict[str, str]) -> None:
    text = SUPP_MD.read_text(encoding="utf-8")
    text = re.sub(
        r"\A# From Primitive Provenance to Mathematical Structure — Supplementary Material\s*\n"
        r"<!-- CNNA-DOCUMENT-METADATA-BEGIN -->.*?"
        r"<!-- CNNA-DOCUMENT-METADATA-END -->\s*\n",
        "",
        text,
        flags=re.S,
    )
    with tempfile.TemporaryDirectory(prefix="cnna_pandoc_") as tmp:
        source = Path(tmp) / "supplementary.md"
        target = Path(tmp) / "supplementary.tex"
        source.write_text(text, encoding="utf-8")
        run(
            [
                "pandoc",
                str(source),
                "-f",
                "markdown+tex_math_single_backslash",
                "-t",
                "latex",
                "--top-level-division=section",
                "--no-highlight",
                "-o",
                str(target),
            ],
            cwd=ROOT,
            env=env,
        )
        converted = wrap_texttt_with_seqsplit(target.read_text(encoding="utf-8"))
        SUPP_BODY.write_text(converted, encoding="utf-8")


def main() -> None:
    env = build_env()
    latex_build(MAIN_TEX, MAIN_PDF, env=env, use_biber=True)
    main_hash = sha256(MAIN_PDF)
    update_supplement_binding(main_hash)
    build_supplement_body(env=env)
    latex_build(SUPP_TEX, SUPP_PDF, env=env)
    print(f"MAIN_SHA256 {main_hash}")
    print(f"SUPPLEMENT_SHA256 {sha256(SUPP_PDF)}")


if __name__ == "__main__":
    main()
