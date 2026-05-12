# Phase 1.1.1.1.5.1.1 / LEG43 — Notation removal review ledger

Status: **closed in P1.44**  
Timestamp: `2026-05-12T11:50:00+02:00`

## Scope

LEG43 consumes the closed LEG42 notation-surface audit and decides which unconsumed `Notation.lean` surfaces may be handed to LEG44 for actual deletion/retirement. This phase is review-only: no Lean source file is changed and no Lean build is claimed.

Input evidence:

- `generated_exports/notation_surface_consumption_cleanup_ledger.generated.tsv`
- `generated_exports/notation_surface_consumption_cleanup_evidence.generated.json`

Output evidence:

- `generated_exports/notation_removal_review_ledger.generated.tsv`
- `generated_exports/notation_removal_review_summary.generated.json`

## Decision criteria

1. Direct non-Notation consumer evidence blocks deletion.
2. Absence of direct consumers is not by itself a deletion proof.
3. Scoped/core-symbol syntax remains deferred because it may be intentional public notation.
4. `CNNA.PillarA.Notation` umbrella aliases remain deferred because they are facade/API surfaces.
5. Domain aliases outside `CNNA.PillarA.Arithmetic.Notation` remain deferred to owner/publicity review.
6. Unconsumed Arithmetic/Notation legacy or phase-domain `abbrev`/`def`/`theorem` surfaces are approved for LEG44 only because their owner objects live in imported source modules and no non-Notation consumer uses the alias surface.
7. Rows with Notation-internal consumers may only be removed as closed dependency clusters in LEG44.

## Counts

| class | count |
|---|---:|
| total LEG42 surfaces reviewed | 1156 |
| consumed, out of removal scope | 484 |
| unconsumed surfaces reviewed | 672 |
| approved for LEG44 total | 494 |
| approved standalone-removal candidates | 391 |
| approved closed-cluster candidates | 103 |
| deferred, not deletion-certified | 178 |

## Review-decision counts

- `APPROVE_LEG44_STANDALONE_REMOVAL_CANDIDATE`: 391
- `APPROVE_LEG44_CLOSED_CLUSTER_REMOVAL_CANDIDATE`: 103
- `KEEP_CONSUMED_OUT_OF_REMOVAL_SCOPE`: 484
- `DEFER_OWNER_DOMAIN_SURFACE_REVIEW`: 101
- `DEFER_CORE_SYMBOL_SURFACE_REVIEW`: 17
- `DEFER_UMBRELLA_FACADE_REVIEW`: 60

## Consequence for next phase

`1.1.1.1.5.1.2` / LEG44 is now the unique active cursor. It may edit only the 494 LEG43-approved Arithmetic/Notation candidates, and only with exact source diffs plus local Lean build/regression evidence. The 178 deferred unconsumed rows are not deletion-authorized by LEG43 and must be handled later by neutral facade/core-symbol/quarantine planning.

## Uncertainty statement

The review is based on static source-token evidence and direct source inspection classes from LEG42. It is strong enough to route a minimal cleanup execution phase, but it is not a substitute for Lean elaboration, external API policy, or a local full build after edits.
