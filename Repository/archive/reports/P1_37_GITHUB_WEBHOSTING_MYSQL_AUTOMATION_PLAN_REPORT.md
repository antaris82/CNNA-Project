# P1.37 GitHub/Webhosting/MySQL automation planning update

Date: 2026-05-12T07:24:59+02:00

## Scope

This planning-data update integrates the GitHub repository automation, mandatory backup, GitHub Actions CI snapshot, Webhosting-local MySQL staging import, read-only public mirror and rollback/local-archive policy into the CNNA planning layer.

## Main changes

- Added Phase `21.2.1`: GitHub repository automation safety contract.
- Added Phase `21.2.2`: GitHub Actions Lean-build and snapshot-artifact pipeline contract.
- Added Phase `21.2.3`: Webhosting-local MySQL staging importer, read-only mirror swap and rollback contract.
- Added Objects `CEX12`, `CEX13`, `CEX14` plus matching proof dossiers and implementation scratchpads.
- Updated Phase `21.2`, `21.3`, `21.4`, `21.5` and `21.9` so the source order is explicit: repository safety -> CI artifact -> Webhosting-local import -> read-only API/UI/deployment.
- Added workflows for backup-gated GitHub automation, CI snapshot/Webhosting-MySQL import and local archival/rollback.
- Added global no-go guardrails `GNG62`-`GNG64`.

## Truth boundary

No Lean source changed. No GitHub workflow, database connection, Webhosting importer or frontend code was created. The update is planning-only plus regenerated secondary documentation. Lean remains the primary truth system; CI, SQL and Explorer layers remain generated-secondary audit/presentation surfaces.
