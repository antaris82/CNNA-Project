# V1.15 Root Lean Toolchain Files Report

## Summary

V1.15 corrects the V1.14 root invariant. The project root is not README-only. It must retain the Lean/Lake project-control files required for local build entry and toolchain reproducibility:

- `CNNA.lean`
- `lakefile.lean`
- `lake-manifest.json`
- `lean-toolchain`

Generated PDF/TeX/LaTeX build products and historical reports remain non-root secondary artifacts.

## Implemented changes

- Copied the user-provided Lean/Lake files into the package root.
- Updated `README.md` to document local `lake build` usage from the package root.
- Updated `scripts/clean_generated_root_artifacts.py` so cleanup preserves Lean/Lake project-control files defensively if they appear in `Repository/`; canonical copies live in the package root.
- Added DBR10, phase 20.10, proof dossier `proof:DBR10`, guardrail GNG28, finding SCF47, and workflow-policy text.

## Verification

- `python3 scripts/generate_tables.py` succeeded.
- `python3 scripts/clean_generated_root_artifacts.py --apply` preserved the root build files.
- Final package-root audit confirms `.gitignore`, `README.md`, `CNNA.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, and `Repository/`; final `Repository/`-root audit confirms only `.gitignore` and `README.md` as active root files there.

No Lean source under `Repository/repo_snapshot/CNNA` was modified, and no Lean build is claimed.
