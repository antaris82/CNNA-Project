# v23 Consumption Classification and Blue-Object Correction Report

Date: 2026-05-09

## Decision

The next implementation frontier is not a direct code deletion or a direct `Legacy.StatusGates` move. It is a classification gate:

**Active phase: 1.1.1.1 - Module and declaration consumption classification.**

The previous Phase 1.1.1 was too coarse because it mixed five work kinds: reachability classification, blue-object semantic correction, public API contract, pruning, and generated-view authority. v23 splits these into child gates.

## Why this change is necessary

Static reachability is not semantic use. A declaration can be reachable because an umbrella or `BuildAll` module imports it, while its actual role is only status marking, audit provenance, legacy compatibility, or a phase alias. Conversely, a non-mainline declaration can still be a proof bridge or audit obligation and must not be deleted blindly.

The current snapshot shows:

- 287 Lean modules
- 724 internal import edges
- 0 missing internal imports
- 8860 declarations in the symbol inventory
- 394 static reference edges
- 1686 referenced symbols
- rough direct scan: about 872 single-constructor inductives across 99 modules

The earlier 749 single-constructor status-enum figure is treated as a narrower subset, not as the full population and not as a deletion/quarantine criterion by itself.

## New subphase structure

| Phase | Purpose | Exit condition |
|---|---|---|
| 1.1.1.1 | Module/declaration consumption classification | Every relevant declaration family has a semantic class: core-computational, proof-bridge, public-wrapper, legacy-status, legacy-policy, phase-alias, audit-only, blue-semantic-correction, dead-candidate, or final-output. |
| 1.1.1.2 | Blue-object semantic correction ledger | Every B-status object has a semantic defect, natural correction phase, allowed temporary consumers, forbidden public consumers, neutral API target, and exit-to-white condition. |
| 1.1.1.3 | Public API contract and consumer whitelist | Phase 3+ allowed/forbidden import and declaration surfaces are explicit. |
| 1.1.1.4 | Pruning/dead-candidate ledger | Deletion candidates are only candidates; no deletion occurs in this phase. |
| 1.1.1.5 | Generated-view authority lock | YAML/PDF/tables/report are synchronized and the next active cursor can move to 1.1.2. |

## Blue-object policy

Blue means: derived-only/proof-carrying evidence exists, but the semantic/API boundary is not yet correct. Therefore blue objects are not dead, but also not public-final.

The affected families are currently:

- Cayley-Dickson structural path: CD0-CD7
- Schur/DtN path: S01-S06
- Operational arithmetic path: O01-O05

These objects may be used only inside their natural correction chain until the neutral API closes. They must not be directly exported through handoffs or consumed as final public API by later phases.

## Pruning policy

No code is deleted in v23. A later deletion may be allowed only if all of the following hold:

1. The declaration/module has a class in the consumption map.
2. It has no public API contract.
3. It is not a proof bridge, provenance/audit record, legacy compatibility surface, or blue-correction artifact.
4. A later implementation phase actually removes it.
5. A local Lean build is confirmed green after removal.

## Updated object/register effects

v23 adds five planning/API-hygiene objects:

- LEG5 - Declaration consumption classification map
- LEG7 - Blue-object semantic correction ledger
- LEG6 - Public API contract and consumer whitelist
- LEG8 - Pruning and dead-candidate ledger
- LEG9 - Generated-view authority and implementation-lock contract

The ordering is intentional: classify first, then blue correction, then public API, then pruning, then generated-view lock.

## Build status

This is a planning/documentation update. The PDF was generated from the YAML-derived tables. No Lean build was run and no Lean build success is claimed.
