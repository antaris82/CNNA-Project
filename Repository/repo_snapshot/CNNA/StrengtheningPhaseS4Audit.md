# CNNA Strengthening Phase S4 audit

Stand of this audit: prepared for the S4 implementation pass on top of the uploaded green S3 tree and aligned with the plan dated 12 April 2026.

This file is prose only. It is not imported by Lean.

## 1. S4 closure target

S4 is the first true downstream unification gate after the S3 IDEAL-side reference closure.
It must not invent a second finite path. Instead it must show that the already closed generic
`ToCStrong -> CutSpec -> RegionCore -> BoundaryPorts -> Approximant` chain really accepts both:

- the concrete IDEAL reference family from S3, and
- the level-variable variation family from S2.

The phase is only closed if both runs enter the same real finite consumer path.

## 2. What this implementation adds

This pass sharpens the existing generic path rather than replacing it.
It adds:

- explicit S4 entry objects `referenceToC` and `variationToC` in `ToC/Concrete`,
- a transported variation-side IDEAL family built from `LevelVariableSubstrate.zeroThread`,
- public alias exposure for the variation-side family on the ToC / Pillar-A notation surfaces,
- and concrete downstream specializations in `Finite/CutSpec`, `RegionCore`, `BoundaryPorts` and `Approximant`.

These specializations are deliberately thin: each of them is just a proof-carrying use of the
already closed generic builder on one of the two legal family entries.

## 3. Why this is the right S4 shape

The plan requires that the S3 reference notation stop being a merely global mirror and start being
visibly consumed in the real downstream path. This pass therefore uses the S3 reference surface
inside `Finite/CutSpec`, including an explicit theorem that identifies the downstream reference run
with `𝓓ref∞[b]`, and addressed cut constructors over `ReferenceIdealAddrOf`.

At the same time, the variation run is kept on the exact same generic consumer path.
So the phase evidence is not prose but typed terms for both:

- reference cut/region/boundary/approximant objects,
- variation cut/region/boundary/approximant objects.

## 4. What this pass still does not claim

This pass does **not** yet internalize operator-side generator inputs.
In particular it does not yet close:

- S5 on `DirichletWeight`,
- S5 on `InteriorInverse`,
- S6 on the shift / stabilization / closure provenance path.

Those remain separate motor-side obligations.

## 5. Regression conditions after this pass

Treat the following as regressions if they appear:

- a reference-only smoke path that bypasses the generic `ToCStrong` entry,
- a variation-only path that reconstructs finite data without the shared builders,
- reintroducing hidden notation mirrors without operational downstream use,
- weakening the dependent carrier types so that the two family runs only coincide prose-wise but not type-wise.
