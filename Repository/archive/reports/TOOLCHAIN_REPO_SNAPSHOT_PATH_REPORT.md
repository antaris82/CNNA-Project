# Toolchain repo-snapshot path update

## Purpose

The planning/documentation tool now treats the checked CNNA Lean tree as living at:

```text
Repository/repo_snapshot/CNNA
```

It no longer requires a top-level `./CNNA` directory.

## Changes

1. `Repository/scripts/build_export_script_v1.8.py`
   - Default Lean repo root is now `Repository/repo_snapshot`.
   - Default Lean source root remains `CNNA`.
   - Default scanned source tree is therefore `Repository/repo_snapshot/CNNA`.
   - Default inventory output is now explicitly `Repository/repo_inventory/raw_export`, which is the location consumed by `generate_tables.py`.
   - Explicit overrides via positional `repo_root`, `--source-root`, and `--output-dir` still work.

2. `lakefile.lean`
   - The `CNNA` Lean library now sets `srcDir := "Repository/repo_snapshot"`.
   - This preserves module names such as `CNNA.Basic` while allowing files to remain in `Repository/repo_snapshot/CNNA`.

3. `Repository/repo_snapshot/CNNA.lean`
   - Added as the actual root module for the configured Lake source directory.

4. `CNNA.lean`
   - Kept only as a top-level compatibility note/wrapper. It is not the Lake source root after this change; direct `lean CNNA.lean` from the package root may require an explicit `LEAN_PATH` including `Repository/repo_snapshot`.

5. `Repository/README.md`
   - Updated with the new default commands and layout.

## Validation performed here

Executed from the package root:

```bash
python3 Repository/scripts/build_export_script_v1.8.py
```

Result:

- modules: 287
- internal edges: 724
- external edges: 43
- graph is acyclic
- no `repo_snapshot.*`-prefixed Lean module names were generated
- first module path example: `CNNA.Basic` from `CNNA/Basic.lean`
- export written to `Repository/repo_inventory/raw_export`

Executed from `Repository`:

```bash
python3 scripts/generate_tables.py
```

Result:

- generated tables from one YAML master
- 189 phases
- 199 objects
- 189 scratch-pad records
- 199 proof-dossier records

## Not performed

No Lean/Lake build was executed in this environment.
