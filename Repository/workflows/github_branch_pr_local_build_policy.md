# GitHub Branch/PR Workflow with Local Lean Build Gate

Status: active workflow policy
Scope: CNNA planning/documentation tool and Lean source snapshot work
Primary branch: `main`
User-side build gate: local `lake build`
Assistant-side write mode: GitHub branch and pull request

## Policy

The default assistant mutation path is:

```text
GitHub branch -> commits -> pull request -> user pulls/checks locally -> local lake build -> green closeout/merge
```

The assistant must not write directly to `main` unless the user explicitly overrides this for a specific action.

For every bounded phase or workflow update that changes repository state:

1. Create or use a dedicated branch from current `main`.
2. Apply changes only on that branch.
3. Modify only task-relevant files.
4. Avoid generated PDFs, generated context docs, full docs, cache, `.lake`, build artifacts, and unrelated README churn unless explicitly requested.
5. Open a pull request against `main` when the change is reviewable.
6. Give the user the branch name and local commands for testing.
7. Treat the user's local `lake build` result as the authoritative build gate.

## Local build gate

Typical branch check:

```bash
git fetch origin
git switch <branch-name>
lake build
```

After merge into `main`:

```bash
git switch main
git pull
lake build
```

The assistant must not claim Lean build success unless Lean was actually built in the active environment. In this workflow, the user's local build report is the evidence.

## Green closeout

A phase may be marked green only after the branch/PR diff is reviewable, unrelated churn is absent, and the user reports a successful local `lake build` or an equivalent verified green gate exists.

## Red build

If the local build is red, do not merge. Keep `main` unchanged. Record the failing branch/commit/modules when supplied, and create or activate the repair phase at the natural source layer instead of patching downstream consumers.

## ZIP fallback

ZIP output is fallback/export/archive only. It is no longer the primary write path once GitHub branch/PR access is available.

## Invariant

```text
main remains clean until the local build gate or an equivalent verified green gate succeeds.
```
