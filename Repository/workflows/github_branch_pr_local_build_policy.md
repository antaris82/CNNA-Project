# GitHub Branch/PR Workflow with Local Lean Build Gate

Status: active workflow policy
Scope: CNNA planning/documentation tool and Lean source snapshot work
Primary branch: `main`
User-side build gate: local `lake build`
Assistant-side write mode: GitHub branch and pull request unless the user explicitly requests a direct main workflow update

## Policy

The default assistant mutation path is:

```text
GitHub branch -> commits -> pull request -> user pulls/checks locally -> local lake build -> atomic green-and-next closeout -> merge/update main
```

The assistant must not write directly to `main` unless the user explicitly overrides this for a specific action or the change is a bounded workflow/policy text update explicitly requested by the user.

For every bounded phase or workflow update that changes repository state:

1. Create or use a dedicated branch from current `main` for Lean/content changes.
2. Apply changes only on the relevant branch or explicitly authorized direct-main workflow update.
3. Modify only task-relevant files.
4. Avoid generated PDFs, generated context docs, full docs, cache, `.lake`, build artifacts, and unrelated README churn unless explicitly requested or policy-facing text really changes.
5. Open a pull request against `main` when the change is reviewable and not explicitly authorized as a direct-main workflow update.
6. Give the user the branch name and local commands for testing when a branch is used.
7. Treat the user's local `lake build` result as the authoritative build gate for Lean/content changes.
8. After a green build, do not perform a standalone green-setting step. The closeout must atomically mark the completed phase green and set the next active phase in the same operation.

## Local build gate

Typical branch check:

```bash
git fetch origin
git switch <branch-name>
lake build
```

After merge into `main` when Lean/content changed:

```bash
git switch main
git pull
lake build
```

The assistant must not claim Lean build success unless Lean was actually built in the active environment. In this workflow, the user's local build report is the evidence.

## Atomic green-and-next closeout

A successful build report does not trigger an isolated "mark current phase green" action.

Instead, the next state update must be one atomic transition:

```text
completed active phase: Y -> G
next selected phase: O/R/W as justified -> Y
all affected scratchpad/object/proof-dossier evidence updated together
```

This avoids the old two-step sequence:

```text
build green -> mark one phase green -> ask/determine next phase -> mark next phase active
```

The assistant should therefore treat messages such as `build is green`, `green`, or `PR/build passed` as permission to prepare one combined closeout-and-next-active update, subject to the usual evidence and provenance rules.

A phase may enter this atomic green-and-next transition only after the branch/PR diff is reviewable, unrelated churn is absent, and the user reports a successful local `lake build` or an equivalent verified green gate exists. For workflow-only or documentation-only changes that do not affect Lean/build-sensitive files, the same atomic state-transition rule applies, but no Lean build success is claimed.

## Red build

If the local build is red, do not merge. Keep `main` unchanged. Record the failing branch/commit/modules when supplied, and create or activate the repair phase at the natural source layer instead of patching downstream consumers.

## ZIP fallback

ZIP output is fallback/export/archive only. It is no longer the primary write path once GitHub branch/PR access is available.

## Invariant

```text
main remains clean until the local build gate or an equivalent verified green gate succeeds; phase closure and next activation happen as one state transition.
```
