# Strengthening Audit: SM3db2eR0 GeneratedDegreeFormulaAudit

## Implemented artifacts

- New Lean module: `CNNA/PillarA/Arithmetic/Smoke/GeneratedDegreeFormulaAuditSM3db2eR0.lean`.
- Build integration: `CNNA/PillarA/Arithmetic/BuildAll.lean` imports the new module immediately after `GeneratedDegreePivotScaleSourceSM3db2dR`.

## Positive-path result

SM3db2eR0 classifies the current generated pivot degree source without creating a scalar inverse. The exposed formula is:

- `generatedDirichlet_degree W i = ∑ j, generatedEntryWeight W i j`.
- `generatedDirichlet_degree W i = ∑ j, if generatedAdjacent i j then W.policy.constantWeight i j else 0`.
- Using `W.policy_eq_input`, the same formula is bound to the input `wp`:
  `generatedDirichlet_degree W i = ∑ j, if generatedAdjacent i j then wp.constantWeight i j else 0`.

The trace pivot entry is also bound through the existing SM3db2cR requirement to this finite generated adjacency/weight-policy sum.

## Derived-only status

- No free scale table was introduced.
- No free reciprocal profile was introduced.
- No scalar inversion path was introduced.
- No `Matrix.inv`, no ProductIdentityProof, no TwoSidedInv, no DtN/GeneralizedDtN/MultiSchur data and no Charpoly/Factor/Discriminant target data were introduced.

## Remaining gate after SM3db2eR0

The current API exposes the generated degree as a finite weighted adjacency sum, not as a constant unit, Nat-cast degree formula, or operational reciprocal datum. Therefore `SM3db2eR` remains the next active phase: build a `GeneratedDegreePivotReciprocalProfileSM3db2dR` from the audited generated degree/weight-policy provenance, or introduce a minimal positive reciprocal-source layer if the formula alone is insufficient.

`SM3eR-r3c1b1` remains blocked until SM3db2eR supplies the unconditional reciprocal profile and the resulting SM3db2dR scale source.
