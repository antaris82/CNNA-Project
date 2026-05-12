# CNNA Strengthening Phase S0 audit after green P27

Stand of this audit: aligned to the Strengthening plan dated 11 April 2026 and reconciled against the uploaded green post-P27 tree.

This file is the S0 repo audit. It is intentionally not imported by Lean.
Its job is to separate Strengthening step 2 terminologically and architecturally from the closed refactor, to record what the active generator path already contains, to mark the real generator bottlenecks, and to pin down which algebraic seeds later pillars actually depend on.

## 1. S0 result in one sentence

Refactor step 1 is over; the active tree is now a single Pillar-A production path whose next work is Strengthening, not more cutover, and the repo audit shows both where the path is already complete and where the true generator bottlenecks still sit.

## 2. Active build topology actually present in the repo

The active root build is already the minimal topology required by the plan:

- `CNNA/BuildAll.lean` imports only `CNNA.Notation` and `CNNA.PillarA.BuildAll`.
- `CNNA/Notation.lean` imports only `CNNA.PillarA.Notation`.
- `CNNA/PillarA/BuildAll.lean` is the only active mathematical aggregate build.
- `CNNA/PillarB` through `CNNA/PillarE` remain active-tree stubs.

S0 conclusion: the build topology itself does not need a second shadow line. The single active production tree is already fixed.

## 3. Import audit of the active Pillar-A tree

A grep-level import audit over `CNNA/PillarA/**/*.lean` shows:

- no imports from `legacy_sources/...`,
- no imports from archived top-level old-path trees,
- no hidden dependency from active Pillar A into later pillars,
- no non-Pillar-A CNNA import except neutral root aggregators such as `CNNA.Basic`/`CNNA.Notation` when applicable.

S0 conclusion: the active Pillar-A tree is already topologically detached from the archived paths. Strengthening can proceed in-place without another architectural cutover.

## 4. Grep-audit of style-relevant residue in the active tree

On the uploaded state after the local cleanup performed in S0, the active tree `CNNA/PillarA` is grep-clean with respect to the following patterns:

- `sorry`,
- `admit`,
- free `axiom`,
- `classical`,
- `noncomputable`,
- `@[simp]`,
- in-code block comments/docstrings.

This is a grep-level audit only. It is not a substitute for a local Lean build, but it is the repo-level evidence required by S0 that the active path is not obviously drifting back into the disallowed old patterns.

## 5. Which builders already stand on the active path

The active Pillar-A tree already contains the full post-cutover module spine from foundation to handoff:

- Foundation: `SubstrateClass`, `MatrixNorms`, `Interfaces`, `Determinism`
- ToC: `Contract`, `Addressing`, `IdealAddressEquiv`, `Concrete`
- Finite: `CutSpec`, `RegionCore`, `BoundaryPorts`, `Approximant`, `Selection`, `DirichletLaplacian`
- DtN: `DtN`, `DtNStabilized`
- Sectors: `BranchPatch`, `ComplementSectorFamily`, `SectorSplit`, `BranchingWitness`, `SelectedBranching`, `UVSpectralSelector`, `BranchingSelector`
- Closure: `ParameterClosure`, `RegularizationClosure`
- Network: `RegionNet`, `InfiniteCarrier`, `SectorChannels`, `SectorSysEnv`, `RelativeEntropyFlow`
- Geometry: `LCPMeasure`, `Foliation`, `SpacetimePaths`
- Coupling: `GeneralizedDtN`, `MultiSchur`
- Handoff: `SectorExport`, `Step1StrongCore`, `Step1MathData`, `ABHandoffStrong`, `PillarAStep1Closed`

S0 conclusion: the task is no longer to recover the post-cutover topology. The task is to strengthen an already continuous root-to-handoff path into a productive generator.

## 6. Real generator bottlenecks still publicly visible in the code

The active tree still exposes the following public generator bottlenecks that Strengthening must address phasewise:

1. `Finite/DirichletLaplacian.lean`
   - public `DirichletWeight`
   - public `weight`, `weight_symm`, `weight_nonneg`
   - meaning: the operator path still expects a free weight witness instead of a policy-driven generator input.

2. `DtN/DtN.lean`
   - public `InteriorInverse`
   - public `interiorInverse`
   - meaning: the binary DtN layer still exposes a free inversion witness instead of a fully internal solver contract.

3. `DtN/DtNStabilized.lean`
   - public `epsilon`
   - meaning: stabilization provenance is visible, but the generator still treats the regularization seed as an external parameter rather than a policy-controlled axis.

4. `Coupling/MultiSchur.lean`
   - public `interfaceInverse`
   - meaning: the Schur layer still expects a free interface inverse witness.

5. `Handoff/SectorExport.lean`
   - re-exports the Schur-side `interfaceInverse`
   - meaning: the export surface is currently still carrying a public trace of an upstream solver bottleneck.

S0 conclusion: these are the real generator engstellen. They are not documentation issues and not notation issues; they are the mathematically relevant strengthening targets.

## 7. Which algebraic seeds later pillars actually need from Pillar A

The audit shows that the active path currently has the numeric/operator spine, but not yet the explicit finite algebraic seed layer that later pillars should consume.

Missing but explicitly plan-required foundation/generator modules include:

- `Foundation/HermitianStructure.lean`
- `Foundation/FiniteHilbert.lean`
- `Foundation/MatrixAlgebra.lean`
- `Foundation/ConcreteSubstrate.lean`
- `Foundation/LevelVariableSubstrate.lean`
- `Foundation/WeightPolicy.lean`
- `Foundation/RegularizationPolicy.lean`
- `Foundation/SubstrateAnalysis.lean`

Still absent but plan-signaled downstream finite seeds include at least the following classes:

- spectral decomposition,
- state-space seeds,
- matrix exponential / time-evolution seeds,
- Gibbs / thermal seed objects,
- dynamics adapters,
- finite algebraic channel/superoperator seeds.

S0 conclusion: later pillars should not rebuild these from scratch. The audit makes explicit that they are genuine A-side strengthening work, not optional garnish.

## 8. Why export and handoff are to be read as pure coupling layers

The active handoff chain is already structurally thin:

- `SectorExportStrong` couples only `InfiniteCarrierStrong`, `RegularizationClosureStrong`, and `MultiSchurStrong` with compatibility equalities.
- `Step1StrongCore` stores only `SectorExportStrong`.
- `Step1MathDataStrong` stores only `Step1StrongCore`.
- `ABHandoffStrong` stores only `Step1MathDataStrong`, together with the outward payload and its equality to the source export surface.
- `PillarAStep1Closed` stores only `ABHandoffStrong`.

S0 conclusion: export/handoff is already architecturally downstream coupling. It is not the place where the missing generator mathematics should be smuggled in.

## 9. Notation reading of S0

The root notation topology is already correct in kind:

- local notation files stay scoped to their fachliche module groups,
- `CNNA/PillarA/Notation.lean` is the single active Pillar-A alias surface,
- `CNNA/Notation.lean` remains the root re-export surface.

S0 conclusion: notation is not the primary blocker. New notation work should follow only when new Strengthening modules actually land.

## 10. Immediate consequences for S1 and beyond

The next phase is not another repo cutover. The next phase is the first genuine generator phase.

That means:

- keep the current active build topology fixed,
- do not reopen archived paths,
- do not add fake scaffold modules outside the real next phase,
- start with the concrete reference substrate and the algebraic foundation seeds that the plan assigns to S1,
- then internalize the public generator bottlenecks phasewise rather than compensating for them in export or handoff.
