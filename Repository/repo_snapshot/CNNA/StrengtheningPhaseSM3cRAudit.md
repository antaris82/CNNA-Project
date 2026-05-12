# Strengthening Phase SM3cR Audit

## Scope

SM3cR adds the generated Interior-block restriction layer after the green SM3bR reset build.

Implemented file:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorBlock.lean`

Updated wiring:

- `CNNA/PillarA/Arithmetic/BuildAll.lean`
- `CNNA/PillarA/Arithmetic/Notation.lean`

## Positive source chain

The implemented chain is:

```text
SM2R GeneratedApproximantStrong
→ SM3aR GeneratedBoundaryInteriorPartition
→ SM3bR generatedDirichletMatrix / generatedDirichlet_entry
→ generatedInteriorBlock_entry
→ generatedInteriorBlock
→ GeneratedInteriorBlockStructureProfile
→ SM3cRGeneratedInteriorBlockLedger
```

## Implemented public surface

- `generatedInteriorBlock_entry`
- `generatedInteriorBlock`
- `generatedInteriorBlock_entry_eq_dirichlet`
- `generatedInteriorBlock_from_dirichlet`
- `generatedInteriorBlock_zero_of_not_adjacent`
- `generatedInteriorBlock_offdiag_of_parent_child_or_coupling`
- `generatedInteriorBlock_diag_degree_or_regularized_degree`
- `InteriorBlockStructureProfile`
- `GeneratedInteriorBlockStructureProfile`
- `SM3cRGeneratedInteriorBlockLedger`
- regular/variable constructors and notation aliases

## Classification decision

The positive profile exposed by this phase is `treeRecursive`.

This is not a diagonal formula and not an inverse formula. It records that Interior-block entries are classified by the generated parent/child-or-coupling adjacency rule inherited from SM3bR. Off-diagonal terms are visible through the conditional off-diagonal theorem; non-adjacent off-diagonal entries are zero through the null theorem; diagonal entries are degree entries through the diagonal theorem.

## Guardrails retained

The ledger explicitly records:

- no free Interior-block table
- no inverse or Interior-elimination formula in SM3cR
- no DtN, GeneralizedDtN, or MultiSchur data in SM3cR
- no charpoly, factorization, discriminant, or L2/L3 target data in SM3cR

## Static local audit performed by ChatGPT

ChatGPT could not run Lean in the container. The following static checks were run over the modified Lean files:

- no `sorry`
- no `admit`
- no new `axiom`
- no operative `noncomputable`
- no `classical`
- no `@[simp]` attribute
- no imported old SM1-SM3d module
- no `Matrix.inv`
- no `TwoSidedInv`
- no Interior-elimination certificate
- no DtN/GeneralizedDtN/MultiSchur construction in SM3cR

## Toolchain note

No new direct `Mathlib.*` import was introduced by SM3cR. The new module imports only the existing project module:

- `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry`

Thus the direct mathlib-import risk introduced by SM3cR is zero beyond the already green SM3bR baseline.

## Remaining gate before SM3dR

SM3dR may start only after the local Lean build is green and after the `treeRecursive` Interior-entry profile is accepted as the intended positive profile. SM3dR must not introduce a diagonal inverse. It must consume the profile and choose a structure-dependent elimination route.
