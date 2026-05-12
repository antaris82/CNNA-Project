# CNNA Strengthening Phase S2 audit

Stand of this audit: prepared on top of the uploaded green S1 tree and aligned with the plan dated 12 April 2026.

This file is prose only. It is not imported by Lean.

## 1. S2 closure target

S2 is the first true motor-side variation phase of the Strengthening block.
It must add three things without reopening the generic Foundation root:

- a second legal substrate family,
- an explicit weight axis,
- an explicit regularization axis,
- and an auditable distinction between universal substrate facts and stronger assumptions.

So the intended S2 reading is not "more helper code", but "the first real variation and provenance surface above S1".

## 2. What this implementation adds

This pass introduces four new Foundation modules:

- `CNNA/PillarA/Foundation/LevelVariableSubstrate.lean`
- `CNNA/PillarA/Foundation/WeightPolicy.lean`
- `CNNA/PillarA/Foundation/RegularizationPolicy.lean`
- `CNNA/PillarA/Foundation/SubstrateAnalysis.lean`

Their intended roles are deliberately separated.

### LevelVariableSubstrate

`LevelVariableSubstrate` adds the first non-reference family
`LevelVariableCell branching L := (i : Fin L) → Fin (branching i.1 + 1)`.
This keeps the root parametric doctrine intact while adding a genuinely different, still computable,
level-dependent branching family.

### WeightPolicy

`WeightPolicy` exposes the thermal provenance axis `β : ℚ` explicitly at Foundation level through
`ThermalAxis` and `WeightPolicy`. The active surface is still intentionally narrow: it gives a visible,
proof-carrying positive rational axis and a canonical constant-weight builder over arbitrary finite
vertex types.

### RegularizationPolicy

`RegularizationPolicy` exposes the canonical positive rational regularization input `ϵ : ℚ`
separately from substrate choice and weight choice. It also binds that input directly to the already
active computable `MatrixNorm.Exec.shift` / `deltaRegularization` surface, so the future S6 path
has a legal Foundation-side provenance source.

### SubstrateAnalysis

`SubstrateAnalysis` makes the assumption hierarchy explicit instead of leaving it prose-only.
The module separates:

- universal `SubstrateClass` facts,
- stronger deterministic facts,
- level-uniform branching facts,
- fully uniform branching facts.

It also exposes a small audit ledger so the intended classification remains grep-visible.

## 3. Why this remains architecturally legal

None of the new modules replaces the generic `SubstrateClass` root.
They sit strictly above it:

- the second family is another concrete witness family,
- the policy modules move visible inputs to the motor side,
- the analysis module classifies assumptions but does not mutate the active semantic root.

So S2 sharpens the generator start conditions without creating a second semantic foundation.

## 4. What this pass deliberately does not yet claim

This S2 pass does **not** yet claim that later consumers already use the new policy surfaces.
In particular it does not yet close:

- S3 ideal-side rebinding of the reference family,
- S4 joint entry of reference and variation families into the same ToC/finite path,
- S5 closure of `DirichletWeight` as an actual consumer of `WeightPolicy`,
- S6 closure of the `ϵ`-axis inside `DtNStabilized` and `RegularizationClosure`.

Those are the next legitimate steps.

## 5. Integration expected from this pass

The new modules are expected to be visible already at the active Foundation and Pillar-A surfaces:

- `Foundation/BuildAll` imports all four modules,
- `Foundation/Notation` mirrors their main public names,
- `PillarA/Notation` mirrors the high-level aliases,
- no downstream module is yet forced to consume them before its own strengthening phase.

## 6. Regression conditions after this pass

Treat the following as regressions if they appear:

- a second semantic root beside `SubstrateClass`,
- hidden reintroduction of `β` or `ϵ` as ad-hoc mid-pipeline parameters,
- analytic regularization logic imported as operative Foundation root,
- policy logic smuggled straight into later operator modules before S5/S6,
- prose claims that universality already covers deterministic or uniform facts.
