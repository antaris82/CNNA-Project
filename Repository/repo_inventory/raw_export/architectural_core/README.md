# Architectural core export

This directory adds a cleaned architectural view on top of the raw import export.

- Artifact modules filtered: **46**
- Core modules retained: **241**
- Clean syntactic signal edges: **307**
- Clean syntactic mainline length: **68**
- Clean semantic mainline length: **56**
- Clean discipline bridges: **4**
- Weak clean-mainline edges: **3**
- Edge-case reports: **3**

## Artifact rules

- `build_module`: file stem `BuildAll`
- `notation_module`: file stem `Notation`
- `top_level_umbrella`: top-level wrapper importing exactly one `*.BuildAll` module
- `umbrella_module`: non-top-level wrapper importing exactly one `*.BuildAll` module and not consumed internally
- `isolated_internal_module`: no internal imports and no internal importers

The cleaned view is diagnostic only. It should be read alongside the raw export, not instead of it.
