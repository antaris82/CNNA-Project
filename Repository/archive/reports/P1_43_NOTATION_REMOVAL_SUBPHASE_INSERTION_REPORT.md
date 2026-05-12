# P1.43 Notation-removal subphase insertion report

Timestamp: 2026-05-12T11:35:00+02:00

## Change

Inserted two missing notation-cleanup subgates before `1.1.1.1.5.2`:

1. `1.1.1.1.5.1.1` — review which LEG42-unconsumed notation surfaces can actually be removed.
2. `1.1.1.1.5.1.2` — remove only genuinely unused notation surfaces, or close as an explicit no-op certificate.

## Rationale

LEG42 is an audit ledger. It proves consumption evidence was collected, but it does not prove deletion safety. Missing direct consumer hits are not enough: a notation may still be intentional public API, a compatibility facade, a legacy/quarantine candidate, an owner-object alias, or documentation/API surface.

## Evidence basis

- Input ledger: `Repository/generated_exports/notation_surface_consumption_cleanup_ledger.generated.tsv`
- Input evidence JSON: `Repository/generated_exports/notation_surface_consumption_cleanup_evidence.generated.json`
- Counts: 1156 surfaces total; 484 with direct non-Notation consumers; 672 without direct non-Notation consumers. Classification counts: {'legacy_phase_alias_candidate': 196, 'consumed_internal_helper': 484, 'unconsumed_domain_alias_candidate': 399, 'unconsumed_symbol_surface_candidate': 17, 'unconsumed_umbrella_alias_candidate': 60}. Disposition counts: {'quarantine_under_legacy_status_or_remove_after_facade_plan': 196, 'keep_now_review_publicity': 484, 'owner_review_keep_internal_or_remove': 399, 'quarantine_or_keep_as_intentional_public_after_phase_1_1_1_1_5_2': 17, 'facade_review_or_quarantine': 60}.

## State changes

- Unique active phase: `1.1.1.1.5.1.1`
- `1.1.1.1.5.1.2`: orange, implementable after LEG43.
- `1.1.1.1.5.2`: demoted from yellow to orange until LEG44 closes.
- New objects: `LEG43`, `LEG44`.
- No Lean code changed.
- No Lean build run or claimed.
- No PDF generated.
