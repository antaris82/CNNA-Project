# v33 General Early Computation Test Matrix Report

## Purpose

v32 had a useful Eisenstein/Gauss lattice test matrix, but it was still too easy to read it as a special-case test suite. v33 changes the planning semantics: Eisenstein/Gauss are sentinel rows inside a general early finite computation test matrix.

## Added planning artifacts

- Green decision gate: `1.1.1.1.0.10 - General early finite computation test-matrix contract and non-specialization lock`.
- Future derivation/test phase: `4.0.1 - General finite computation test matrix before operational arithmetic wrappers`.
- New objects: `LEG29` and `O07`.
- New global guardrail: `GNG16 - no special-case-only test matrix as evidence for a general computable path`.
- New workflow: `General early finite computation-test matrix`.

## Semantics

The general rows must consume the code-defined generator/branching API and produce finite/rational/integer executable witnesses. Sentinel rows such as Eisenstein/Gauss may add comparison-only fields such as angle profile, tau, CM point, discriminant target, and j target, but they cannot replace generic finite coverage.

## Phase-order effect

The new green gate is before the active cursor, so the active module-manifest phase must now also decide where generic finite tests live and how they reuse the canonical smoke-test generator. The future Phase 4.0.1 is inserted before operational arithmetic wrappers, so early computations are tested generally before specialized lattice/CM interpretation.

## Validation

`generate_tables.py` generated tables successfully from one YAML master with 174 phases, 184 objects, 174 scratchpad records, and 184 proof dossiers. PDF compilation is performed separately. No Lean build was run.
