# Phase 1.1 refinement report for CNNA planning v22

## Decision

The next active frontier is no longer the broad Phase 1 umbrella. It is now Phase 1.1.1: **Notation/legacy split inventory and generated-view authority lock**.

## Why Phase 1.1 was split

The previous Phase 1.1 combined several different work kinds:

1. classify the 5095-line `Arithmetic/Notation.lean` monolith;
2. quarantine the 749 single-constructor status enums;
3. extract a true small notation/core-symbol surface;
4. separate legacy phase aliases from neutral wrappers;
5. verify that later phases, especially Phase 3+, cannot import legacy gates.

Keeping those in one implementation phase would hide import failures and make consumer-side patching likely. v22 therefore splits Phase 1.1 into five subphases.

## New Phase 1.1 subphases

- **1.1.1** - Notation/legacy split inventory and generated-view authority lock. Active. Planning/audit gate only; no Lean semantic declaration moves.
- **1.1.2** - Quarantine single-constructor legacy status gates in `CNNA/PillarA/Arithmetic/Legacy/StatusGates.lean`. Do not delete them.
- **1.1.3** - Create the true `CoreSymbols`/notation micro-surface.
- **1.1.4** - Separate legacy phase aliases from neutral wrappers.
- **1.1.5** - Run the post-split import firewall and Phase-3 visibility gate.

## Corrected adjacent phase hierarchy

The former 1.5-1.9 generated object phases created a semantic clash: for example, `G03 Level / Cutoff` pointed into Phase 1.4 although Phase 1.4 was Cayley-Dickson reintegration. v22 fixes the hierarchy:

- **1.2.*** - ExecComplex, generator provenance, substrates, level/cutoff, carrier/index.
- **1.3.*** - partition, regime split, complement families.
- **1.4.*** - Cayley-Dickson structural reintegration.

## Authority cleanup

The YAML master remains the only maintained planning source. v22 uses a v22 main TeX/PDF filename. Old v20/v21 TeX/PDF files are historical outputs only and should not be edited as roadmap sources.

## Build status

This report concerns planning artifacts and generated views. No Lean build was run. Lean build success must be supplied by an actual current build or by the user's local build report.
