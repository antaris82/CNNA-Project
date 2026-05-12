# Strengthening Phase SM3bR Audit

## Scope

SM3bR adds the first generated Dirichlet entry layer after the green SM3aR reset build.

Implemented file:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedDirichletEntry.lean`

Updated wiring:

- `CNNA/PillarA/Arithmetic/BuildAll.lean`
- `CNNA/PillarA/Arithmetic/Notation.lean`

## Positive source chain

The implemented chain is:

```text
SM2R GeneratedApproximantStrong
→ SM3aR GeneratedBoundaryInteriorPartition
→ GeneratedAdjacencySource
→ GeneratedWeightPolicyEntrySource
→ generatedDirichlet_entry
→ generatedDirichletMatrix i j := generatedDirichlet_entry i j
```

## Implemented public surface

- `GeneratedAdjacencySource`
- `GeneratedWeightPolicyEntrySource`
- `GeneratedDirichletEntrySource`
- `generatedForwardAdjacent`
- `generatedAdjacent`
- `generatedEntryWeight`
- `generatedDirichlet_degree`
- `generatedDirichlet_entry`
- `generatedDirichletMatrix`
- `zero_of_not_adjacent`
- `offdiag_of_adjacent`
- `diag_degree_or_regularized_degree`
- `boundary_entry_from_generated_source`
- `interior_entry_from_generated_source`
- `SM3bRGeneratedDirichletEntryLedger`
- regular/variable constructors and notation aliases

## Guardrails retained

The ledger explicitly records:

- no free adjacency relation
- no free weight function
- matrix exposed only through the entry function
- no Interior-block profile in SM3bR
- no inverse or Interior-elimination in SM3bR
- no DtN, GeneralizedDtN, or MultiSchur data in SM3bR

## Static local audit performed by ChatGPT

ChatGPT could not run Lean in the container. The following static checks were run over the Smoke/Notation/BuildAll surface:

- no `sorry` in modified Lean files
- no `admit` in modified Lean files
- no new `axiom` in modified Lean files
- no operative `noncomputable` in modified Lean files
- no `classical` in modified Lean files
- no `@[simp]` attribute in modified Lean files
- no imported old SM1-SM3d module
- no `Matrix.inv`
- no Interior-elimination certificate
- no DtN/GeneralizedDtN/MultiSchur construction in SM3bR

## Toolchain note

No new direct `Mathlib.*` import was introduced by SM3bR. The new module imports only already-existing project modules:

- `CNNA.PillarA.Arithmetic.Smoke.GeneratedBoundaryInteriorPartition`
- `CNNA.PillarA.Foundation.WeightPolicy`

Thus the mathlib-import risk introduced by SM3bR is zero beyond the already green SM3aR baseline.

## Remaining gate before SM3cR

SM3cR may start only after the local Lean build is green. SM3cR must consume `generatedDirichletMatrix` and classify the Interior-block entry structure. It must not assume diagonal form; Parent/Child couplings between Interior nodes must be made visible if present.
