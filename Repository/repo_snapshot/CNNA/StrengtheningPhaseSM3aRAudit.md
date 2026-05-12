# Strengthening Phase SM3aR Audit

Status: implementation patch prepared for local Lean build.

Scope: SM3aR starts from the green SM2R generated approximant core and adds only the boundary/interior partition layer.

Implemented Lean surface:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedBoundaryInteriorPartition.lean`
  - `GeneratedApproximantIndex` as a proof-carrying dependent index over `Fin (p.L_max + 1)` and membership in `A.approximant.carrier`.
  - `GeneratedBoundaryPredicate`: level equals the SM2R policy cutoff `p.L_max`.
  - `GeneratedInteriorPredicate`: level is strictly below `p.L_max`.
  - `GeneratedBoundaryIndex` and `GeneratedInteriorIndex` as subtypes of `GeneratedApproximantIndex`.
  - `GeneratedApproximantCarrier`, `GeneratedBoundaryCarrier`, `GeneratedInteriorCarrier`.
  - subset lemmas `boundary_subset_approximantCarrier` and `interior_subset_approximantCarrier`.
  - membership/projection lemmas for boundary and interior indices.
  - partition lemmas `boundaryInterior_disjoint` and `boundaryInterior_complete`.
  - finite/decidable API package `GeneratedPartitionFiniteAPI`.
  - packaged partition `GeneratedBoundaryInteriorPartition`.
  - regular/variable constructors and `SM3aRGeneratedPartitionLedger`.

Compile-feedback correction:

- Fixed the namespace-shadowing error inside `GeneratedBoundaryInteriorPartition.fromApproximant`: structure field projections named `boundary_subset_approximantCarrier`, `interior_subset_approximantCarrier`, `boundaryInterior_disjoint`, and `boundaryInterior_complete` shadowed the outer partition lemmas. The constructor now calls the outer lemmas with fully qualified names.

Import and notation integration:

- `CNNA/PillarA/Arithmetic/BuildAll.lean` imports the new SM3aR module.
- `CNNA/PillarA/Arithmetic/Notation.lean` imports the new SM3aR module and exposes `StrengtheningSM3aR` aliases and ledger entry points.

Negative-surface audit for the new module:

- No `sorry`.
- No `admit`.
- No `axiom`.
- No `noncomputable`.
- No `classical`.
- No `@[simp]` attribute.
- No `CutSpec` import.
- No `BoundaryPorts` import.
- No matrix, Dirichlet, DtN, inverse, two-sided inverse, charpoly, factorization, discriminant, CM, L2 or L3 target data introduced.

Derived-only status:

- Every public boundary/interior index carries a membership proof into the SM2R approximant carrier.
- The only finite level index is `Fin (p.L_max + 1)`, derived from the SM2R policy/cutoff, not a free replacement carrier.
- Boundary and interior are predicates on that proof-carrying approximant index, not external carriers.

Tooling caveat:

- The ChatGPT environment has no local `lean`/`lake` executable. The final proof of green status remains the user's local `lake build`.
