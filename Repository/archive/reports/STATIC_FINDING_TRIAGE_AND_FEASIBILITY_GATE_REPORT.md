# v44 Static Finding Triage and Feasibility Gate

## Purpose

This package corrects a workflow weakness found before starting Phase 1.1.1.2: the existing Static code findings section recorded risks, but did not force a visible lifecycle status, priority, or addressing phase per finding.

## Changes

- Added mandatory fields to every `code_audit` row:
  - `ID`
  - `Priority`
  - `Issue status`
  - `Addressing phase`
- Added priority convention:
  - `R` / red = urgent
  - `Y` / yellow = critical
  - `G` / green = nice-to-have
- Added generator validation in `scripts/generate_tables.py`:
  - every static finding must have an ID,
  - IDs must be unique,
  - priority must be exactly `R`, `Y`, or `G`,
  - issue status and addressing phase must be non-empty.
- Added workflow policy row: `Pre-start feasibility and static-finding triage`.
- Added three new static findings from the review:
  - `SCF24`: missing static-finding lifecycle fields, closed by v44 generator update;
  - `SCF25`: implicit pre-start feasibility gate, closed by v44 workflow update;
  - `SCF26`: blue correction cannot rely only on status-B labels, assigned to active Phase 1.1.1.2.

## Feasibility decision for next phase

Phase 1.1.1.2 is feasible as an infrastructure-only ledger phase. The positive path is to generate/validate a per-blue-object correction ledger from the existing object register, proof dossiers, and consumption-classification exports. The phase must not whiten blue objects, delete objects, or expose public wrappers.

## Build status

No Lean source was changed. No Lean build was run in this package. The prior green Lean build is only the user-reported baseline.
