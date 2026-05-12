# CNNA Strengthening Phase S7 audit

Stand of this audit: extended through the first S7b implementation pass on top of the uploaded green S7a tree and aligned with the plan dated 17 April 2026.

This file is prose only. It is not imported by Lean.

## 1. S7a closure target

S7a closes the coupling-side generator bottleneck directly after the completed S6 closure and S6c handoff reordering.
It must make two points explicit on the same active coupling path:

- `GeneralizedDtNStrong` must carry the raw / stabilized duality as an explicit, theorem-backed coupling surface.
- `MultiSchurStrong` must stop treating `interfaceInverse` as a free root input and instead consume an internalized interface-elimination surface over the stabilized interface block.

## 2. What this implementation changes

This pass reshapes the coupling modules as follows.

- `GeneralizedDtN.lean` receives explicit S7 reference / variation family builders so the coupling stage can be instantiated on the same shared reference and variation runs as the earlier generator stages.
- `MultiSchurStrong` is no longer organized around a naked `ofGeneralizedDtN ... inv hinv` root-input constructor.
  Instead it is driven by a classified `InterfaceEliminationData` surface, analogous to the S5 binary-DtN elimination boundary.
- `InterfaceEliminationMode` records whether the present population came from an explicit inverse, a stricter reduction step, or a fallback mode.
- The public Schur-facing block surface is now the stabilized coupling block surface.
  Raw restricted blocks remain visible only as an explicit audit / diagnostic companion via `rawBlock` and the corresponding raw block projections.
- S7 family builders are added for `referenceFullGeneralizedDtN`, `variationFullGeneralizedDtN`, `referenceFullMultiSchur`, and `variationFullMultiSchur`.

## 3. Why this is the right S7a shape

The plan explicitly forbids repairing coupling weaknesses later in export or handoff modules.
So the coupling boundary itself has to say which operator provenance is raw, which is stabilized, and which one drives the operative Schur path.
This pass therefore keeps both surfaces visible but gives the operative `block` / `interfaceBlock` / Schur formulas only the stabilized provenance.

At the same time the old loose inverse screw is pushed behind a public elimination contract.
The visible export target is not "an arbitrary matrix someone handed us", but

- a classified interface-elimination mode,
- the induced inverse surface,
- and the correctness theorems showing that the stabilized interface block is inverted.

That is the exact S7a analogue of what S5 already did for the interior elimination of the binary DtN stage.

## 4. What this pass still does not claim

This pass does **not** yet prove that every legal coupling instance is canonically populated by a fully derived algorithmic interface reduction.
What it closes is the public architecture boundary:
`interfaceInverse` is no longer treated as the defining root input of the Schur stage, and the operative Schur formulas are no longer allowed to drift back to the raw restricted block path.

A later strengthening step may still sharpen the current interface elimination contract from an explicit inverse-backed instance to a stricter derived reduction law.

## 5. Regression conditions after this pass

Treat the following as regressions if they appear:

- reintroducing a public `ofGeneralizedDtN ... inv hinv`-style root-input constructor on the S7 MultiSchur boundary,
- letting `block`, `interfaceBlock`, or the Schur formulas consume `source.restrictedBlock` / raw restricted data instead of the stabilized block surface,
- hiding the raw block path completely so that no audit / diagnostic surface remains,
- or bypassing the S7 family builders with a separate reference-only or variation-only coupling shortcut.


## 6. S7b carrier closure target

S7b closes the late carrier stage after the coupling-side S7a sharpenings.
It must make three points explicit on the same active path:

- `InfiniteCarrierStrong` remains a strict consumer of the already closed network stage and must not drift into a coupling-side replacement path.
- Stable finite excerpts of the ideal carrier must be exportable as explicit truncations of the same directed family, so later comparison and limit modules can reuse them without reconstructing the carrier semantics.
- The active reference and variation generator runs must reach `InfiniteCarrierStrong` over the same legalized weight / elimination / stabilization path that already drives the earlier generator stages.

## 7. What this S7b pass changes

This pass extends the network-side carrier surface as follows.

- `RegionNet.lean` now exposes `referenceFullRegionNet` and `variationFullRegionNet` as canonical family builders over the stabilized binary DtN path.
- `InfiniteCarrier.lean` now carries explicit `stableExcerpt`, `currentExcerpt`, top-slice, root, and monotonic carrier-agreement theorems for truncation-stable finite excerpts of the same ideal family.
- `referenceFullInfiniteCarrier` and `variationFullInfiniteCarrier` now tie the late carrier stage back to the same active reference / variation generator path instead of leaving that final carrier binding as a manually populated surface.

## 8. What this pass still does not claim

This pass does **not** yet provide AQFT-level quasilocal completion, Type-III semantics, or a full directed-limit object.
What it closes is the carrier-side export boundary required by the plan: a late derived carrier stage with explicit stable excerpts, directed comparison lemmas, and canonical family builders over the already legalized early generator path.

## 9. Regression conditions after S7b

Treat the following as regressions if they appear:

- rebuilding the late carrier stage directly from coupling or handoff modules instead of consuming the closed network surface,
- dropping the explicit stable-excerpt surface so later limit / comparison modules would need to reconstruct truncation semantics ad hoc,
- or reintroducing a separate reference-only or variation-only carrier shortcut outside the shared active builder path.


## 10. Continuation after the green S7b build

After the green S7b build, the next safe code-level continuation inside the already active P23 area is
not another carrier-side semantic fork, but the missing canonical family builder surface for
`SectorChannelsStrong`.
This keeps the late network / channel side aligned with the same shared reference / variation path that
already reaches `GeneralizedDtNStrong`, `RegionNetStrong`, and `InfiniteCarrierStrong`.

This continuation therefore adds:

- `referenceFullSectorChannels`
- `variationFullSectorChannels`

Both are strict wrappers over the already legalized S7 coupling builders and do not introduce a second
network path, a coupling shortcut, or any handoff-side backdoor.

## 11. Assessment of phases beyond S7b

No hard architectural rewrite of phases beyond S7b is forced by the green S7b result itself.
In particular:

- `S8` remains the next actual generator-facing phase, because the network / carrier side is now sufficiently tied back to the shared active builder path.
- `S10a` does not need a dependency rewrite; its stated legal predecessors `RegionNet` and `SectorChannels` remain correct.

A possible later sharpening is to split `S8` internally into an earlier spectral-surface step and a later
full projector package if the strict derived-only / computability discipline makes a one-shot spectral
closure too coarse. That is currently a recommendation, not a blocker, and therefore not yet treated
as a mandatory plan change.
