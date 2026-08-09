# CNNA (ComplemeNt Net Architecture)

## From Primitive Provenance to Mathematical Structure

**A Response-Coupled Derivation on a Growing $b$-ary Tree**

The name **ComplemeNt Net Architecture** identifies the project-wide construction principle. The same growing provenance net is repeatedly separated into a realized or retained part, a relative complement, and an interface through which effective response and the next growth step are determined. This architecture begins with the empty-carrier/root transition, becomes explicit in the born-prefix/open-slot distinction, and continues through Schur/DtN cuts, record/live dynamics, nested channels, and later OQS/AQFT specializations.

Framework context: **Generalized Open Provenance Systems**. The current package formalizes the finite deterministic CNNA specialization; universal completion and later OQS/POVM/AQFT specializations retain their explicit nodewise status.

This package contains the current CNNA registry, mathlib-free Core, proof sources, canonical yEd Live DAG, paper, supplement, reference registry, and validation artifacts.

P001 is kernel-verified under Lean 4.31.0 with mathlib v4.31.0: all 142 registered declarations passed the axiom audit and full package-boundary audit. M003 and M004 are kernel-verified through 11 public closure and handoff declarations with exact current-source evidence.

P002 has the corrected static contract. Its six public declarations package the C018 strict total order on provenance addresses, the extensional order on selected open-slot children, and minimal selected-child uniqueness. State-dependent least-open existence, uniqueness, saturation behavior, and executable-selector agreement remain owned by C004. P002 is kernel-verified under Lean 4.31.0: all six public declarations have empty axiom profiles, and the full package-boundary audit passes. C018 is therefore fully green.

C008 is now also kernel-verified and exact-source bound. It applies the canonical M004 birth instruction to separate append-only record/live channels: record receives only the parent/newborn birth pair, while live additionally receives ancestor and sibling backreaction. Seven C008 declarations passed the axiom audit (3 with `propext`+`Quot.sound`, 4 additionally with transitive `Classical.choice`), the Python regression reports 106 tests / 1086 subtests PASS, and the full package-boundary audit passes. C016 and C017 are both kernel-verified exact-source projections of the C008 record/live update; C009 is kernel-verified as the raw codomain assembly; T002 is now kernel-verified as the recurrent C005 re-entry theorem, and T003 is the single active node.

C016 and C017 are kernel-verified and exact-source bound. C016 projects the immutable record channel and proves the universal one-step left-prefix/parent-child-only contract; C017 projects the current live channel and its complete M004 parent-child + ancestor + sibling delta. Both respect the C006 `SameValue` boundary. Twelve declarations passed the shared C016/C017 axiom audit (2 with `propext`+`Quot.sound`, 10 additionally with transitive `Classical.choice`), the Python regression reports 114 tests / 1086 subtests PASS, and the full package-boundary audit passes. Arbitrary-many future record invariance is deliberately not claimed before recurrent successor closure, and live-minus-record backreaction current remains owned by C024. C009 and T002 are kernel-verified; T003 is the single active DAG node.

The admitted transitive trust profile for verified proof nodes is limited to `propext`, `Classical.choice`, and `Quot.sound`. No project-local axiom or `sorry` is admitted.

Verification command:

```bash
cd derivation/code/lean
./audit/run_package_boundary_audit.sh --build
```

T002 is kernel-verified and exact-source bound. It proves recurrent re-entry into the complete C005 schema and post-step C005↔C017 live coherence. Required local facts are closed at their semantic origins (C004/C005/C006/C007/M001/M004), not hidden inside T002. All 26 audited declarations pass with no project-local axioms or sorry; the Python regression reports 120 tests / 1086 subtests PASS as finite countercheck evidence. T003 is the single active node.
