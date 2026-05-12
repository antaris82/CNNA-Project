# Phase 1.1.1.1.5.2 — Workflow acceleration and repeatability audit

Status: yellow-active
Started: 2026-05-12
Branch: `phase/1.1.1.1.5.2-workflow-audit`
Scope: workflow/tooling only; no Lean source change

## Purpose

This phase turns repeated assistant-side CNNA maintenance work into faster, bounded, reproducible workflows. The immediate trigger is the observed overhead in routine green closeout, cleanup, branch handling, and documentation regeneration.

The phase is not a mathematical derivation phase. It is a workflow/tooling governance phase inside the planning/documentation tool. It must not claim derived-only mathematical closure and must not change Lean semantics.

## Acceleration rule

Every routine task should start from a fixed contract instead of rediscovering the procedure:

```text
phase id -> active cursor check -> allowed file classes -> prohibited churn -> exact write set -> local build gate -> closeout evidence
```

The assistant should therefore first identify the task class, then apply the matching workflow. Free-form planning is reserved for genuinely new mathematical/provenance questions.

## Global defaults introduced by this phase

1. Do not regenerate full PDFs, context docs, generated docs, or TeX build products unless the user explicitly asks for them.
2. Do not update the root README for every phase. Update it only when user-facing operation, installation, policy, or version information materially changes.
3. Keep only one active root README. Do not create duplicate README files in subdirectories unless a specific subproject needs a local operational manual.
4. Prefer small commits on a dedicated branch over full zip turnover once GitHub write access is available.
5. Treat the user's local `lake build` result as the green gate unless an equivalent verified CI gate exists.
6. If a phase only changes planning/tooling state, mark it as workflow/tooling, not Lean-derived mathematics.
7. If a required structure is missing, create or activate the predecessor at the natural source layer; do not patch a downstream consumer.

## Workflow audit matrix

| Workflow | Current risk | Acceleration decision |
|---|---|---|
| Implementability dry run | Repeated rediscovery of dependency checks. | Use a fixed preflight: phase id, dependencies, linked objects, module seams, natural-backjump candidate, prohibited patterns. |
| Green closeout | Too much time spent deciding which files to touch. | Closeout touches only phase status/scratchpad/proof dossier/object evidence and minimal generated views requested by the user. README stays unchanged unless policy/version changed. |
| Red build repair | Risk of downstream patching under time pressure. | Always record failing branch/commit/modules and backjump to the natural origin phase. |
| Context documentation | Context/generated docs can become churn and slow branch operations. | Generate only on explicit request or when a context packet is the deliverable. Otherwise keep deleted/absent. |
| Expert-review dossier | Risk of mixing established theory into CNNA input. | Keep reference theory blue/comparison-only; record open review questions and proof obligations separately. |
| Semantic module consolidation | Risk of flattening provenance-carrying module chains. | Merge only when semantic content is preserved or clarified; keep proof-stage chains separate when boundaries encode derivation order. |
| Source/theory ingestion | Risk of treating external theory as generator. | Extract target objects, comparison theorems, and review gates only. Do not import them as ontic CNNA inputs. |
| Root/build-entry hygiene | Root clutter slows inspection and confuses source/control status. | Preserve only root source/control files and Lean/Lake entry files; generated artifacts are disposable outputs. |
| GitHub branch/PR workflow | Branch divergence can obscure the actual phase diff. | Start each new phase branch from current `main`; if an old branch diverges, do not continue it unless intentionally rebasing/merging. |

## Phase-start checklist

For future phase-start tasks, apply this checklist before writing:

```text
1. Identify current main commit and whether an existing branch is clean or diverged.
2. If the branch is diverged or semantically stale, create a fresh phase branch from main.
3. Locate the active cursor from the master/source files if available.
4. If the authoritative master is unavailable or empty, create only explicit sidecar workflow evidence and do not fabricate master-plan semantics.
5. Declare whether the task is Lean, planning, tooling, documentation, or generated-output work.
6. Write only files belonging to that class.
7. Open a PR when the diff is reviewable.
8. Wait for the user's local build/evidence before green closeout.
```

## Closeout condition

Phase 1.1.1.1.5.2 may become green only when:

- the workflow audit rules above are accepted or integrated into the authoritative planning source,
- any required generated views are regenerated locally from the real Master YAML,
- the branch diff contains no unrelated generated-documentation churn,
- the user reports the relevant local check/build result.

## Non-claims

This file is workflow evidence only. It is not a Lean proof object, not a generated table, and not a substitute for the Master YAML once the Master YAML is available with content.
