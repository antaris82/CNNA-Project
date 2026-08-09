# 030 · C009 — Codomain state Xₙ₊₁

**Canonical node label:** `030 · C009`  
**Semantic ID:** `C009`  
**Current section path:** `1.4.4`  
**Documentation tier:** `D1`  
**Documentation state:** `COMPLETE_V2`  
**Formal state:** `KERNEL_VERIFIED_EXACT_SOURCE_EVIDENCE`

## Position In Derivation
C009 is the first merge point between the C005 recurrent state schema and the already kernel-verified C016/C017 channel projections. It consumes the canonical C004 next slot as carried by the M004 instruction. The next theorem node is T002, which must show that the raw C009 codomain re-enters C005.

## Mathematical Contract
For one `ResponseCapableState X`, one `NextOpenSlot X`, coherent current record/live channels, and one `ResponseCoupledBirthInstruction` typed at that slot, C009 assembles the unique raw codomain data

`(schedule, bornNonRoot, record, live)`

with:

1. `schedule = X.schedule`;
2. `bornNonRoot = X.bornNonRoot ++ [next.val]`;
3. `record = C016.afterInstruction channels instruction`;
4. `live = C017.afterInstruction channels instruction`.

The C005↔C017 boundary is represented by `StateChannelCoherent`: the pre-step live channel must be `DirectedRelationUpdatesSameValue` to the ordered C005 conductance list after the already-defined exact-fraction representation map.

## Introduction Reason
C016 and C017 intentionally stop at their channel projections. C005, by contrast, packages the state-level carrier and conductance invariants. C009 is therefore needed as a non-dynamical assembly boundary before T002 can ask whether one response-coupled step closes back into the same state schema.

## Explicit Construction
Lean defines `CodomainAssemblyInput`, `CodomainStateData`, and `assemble`. Python exposes the corresponding frozen `CodomainStateData` and `assemble_codomain_state_data`. No response scalar, rank force, depth attenuation, schedule policy, new coefficient, or Legacy node-load rule is introduced in C009.

## Invariants
1. The canonical schedule is inherited literally.
2. The born non-root prefix changes by exactly one append of the C004-selected child.
3. The record field is exactly C016; C009 defines no second record law.
4. The live field is exactly C017; C009 defines no second live law.
5. The pre-step C017 live channel must represent the current C005 conductance list.
6. C006/M004 representative changes are propagated only through `SameValue`.
7. No full C005 schema-closure field is constructed inside C009.

## Canonicity Or Uniqueness
`IsCodomainAssembly input output` is the extensional specification `output = assemble input`. `codomainAssembly_existsUnique` proves, without a mathlib dependency in the Core, that one fixed admissible input has exactly one raw codomain output. The earlier `∃!` parser issue was only notation; the verified source uses the equivalent explicit existential-plus-uniqueness form.

## Boundary Cases
An incoherent C005/C017 pre-state is rejected by the Python boundary check and is not an admissible `CodomainAssemblyInput` in Lean. An instruction at a non-canonical slot is likewise rejected in Python; Lean types the instruction at the supplied `NextOpenSlot`. C009 does not claim that every raw output satisfies `bornWithinCutoff`, `bornOrdered`, `bornInitial`, conductance support/positivity/ordered-pair uniqueness, or `parentBackbone`. Those are T002 closure obligations, with any missing supporting lemma repaired at its semantic owner.

## Python Lean Cross Layer
Both layers explicitly assemble the same four components: schedule, born prefix, record and live. Python uses tuples and can attempt a finite `ResponseCapableState` realization for regression. Lean keeps the raw codomain separate from the C005 structure so that the universal schema-closure theorem cannot be smuggled into a constructor.

## Countercheck
The finalized Python suite reports `117 tests, 1086 subtests PASS`. C009-specific tests verify exact C004/C016/C017 component assembly, rejection of an incoherent C005↔C017 handoff, and small finite realizations of the candidate as a C005 state. The realization sweep is explicitly `FINITE_REGRESSION_EVIDENCE_ONLY`; it is not the T002 theorem.

## Result
The user-local Lean 4.31.0 build on 2026-08-08 successfully builds `S04_C009_CodomainStateX`, `CNNAProofs.C009.S01_CanonicalCodomainStateAssemblyClosure`, and `CNNAProofs.C009`. It reports `C009_CURRENT_PROOF_AXIOM_AUDIT PASS`, `c009 = KERNEL_VERIFIED_CURRENT_BUILD`, `c009_codomain_assembly_olean: true`, all predecessor exact-source hash gates true, and `FULL_PACKAGE_BOUNDARY_AUDIT PASS`.

The retained build transcript SHA-256 is `d5d4a0734f9c58d78d905e4ee0532e81ea3940015d77107b1301ca96240b3267`.

Axiom-profile counts over the eight audited declarations are:

- `choice_propext_quot`: 2;
- `propext_quot_only`: 4;
- `axiom_free`: 2.

There is no project-local axiom and no `sorryAx`.

## Downstream Handoff
C009 supplies the deterministic raw codomain to T002. T002 is now kernel-verified and closes the load-bearing recurrent C005 re-entry together with post-step C005↔C017 live coherence. The next active node is T003; C010 is dependency-ready from C009+C018 but remains later in canonical order.

## Code Anchors
- Python assembly source: `s04_c009__codomain_state_x.py`, lines 40–119.
- Python counterchecks: `test_s04_c009__codomain_state_x.py`, lines 48–95.
- Lean Core handoff and assembly: `S04_C009_CodomainStateX.lean`, lines 43–203.
- Lean proof facade: `S01_CanonicalCodomainStateAssemblyClosure.lean`, lines 19–37.
