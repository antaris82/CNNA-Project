# v38 Phase-object-link policy

## What was corrected

v37's phase table rendered `Linked objects` by a single direct rule:

```text
object.Phase == phase.Phase
```

That rule is correct for **object ownership**, but insufficient for the generated PDF view. A phase may intentionally have no direct objects because it is an umbrella, baseline, audit/closeout, or moved placeholder. In v37 this produced blank-looking cells that required manual interpretation.

v38 makes the interpretation explicit and global.

## New global policy

Each phase now has an explicit `Object link policy`:

- `direct` - the phase directly owns one or more registered objects.
- `scope_only` - the phase is an umbrella/routing phase; child phases own the registered objects.
- `no_direct_object` - the phase intentionally has no direct object, e.g. baseline/audit/closeout/infrastructure.
- `moved` - historical placeholder or routing note; active ownership is elsewhere.

Direct ownership remains exact and is not changed by display logic:

```text
object.Phase == phase.Phase
```

Child object scope can be displayed for navigation, but it does not transfer ownership from child phases to the umbrella phase.

## New planning artifacts

- **Phase 1.1.1.1.0.15** - Global phase-object-link policy: no ambiguous empty Linked-objects cells.
- **LEG34** - Phase-object-link policy contract.
- **GNG21** - no unexplained empty Linked-objects cell and no umbrella aggregation as direct object ownership.
- **Workflow** - Phase-object-link policy workflow.
- New top-level YAML table: `phase_object_link_policy`.
- New generated table: `tables/phase_object_link_policy.tex`.

## Generator behavior

The generator now renders `Linked objects` policy-aware:

- direct phases show object hyperlinks;
- scope-only phases show `scope-only; child objects: ...`;
- objectless phases show `no direct object: ...`;
- moved phases show `moved: ...`.

The generator validates policy consistency. For example, a phase declaring `direct` without direct objects fails; a phase declaring `scope_only` without child-object scope fails.

## Validation

- 188 phases
- 198 objects
- 188 scratchpad records
- 198 proof-dossier records
- Object-link policy counts:
  - direct: 152
  - scope_only: 24
  - no_direct_object: 10
  - moved: 2
- exactly one active cursor: `1.1.1.1.1`
- no white phase before the active cursor
- generated tables rebuilt from the YAML master
- PDF compiled with `pdflatex` twice: 231 pages
- sample pages rendered: 1, 4, 70, 220
- no Lean build was executed or claimed
