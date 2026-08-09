# 007 · P002 — Canonical schedule strict-total-order closure

**Canonical node label:** `007 · P002`  
**Semantic ID:** `P002`  
**Current section path:** `1.1.6.1`  
**Documentation tier:** `D2`  
**Documentation state:** `COMPLETE_V2`  
**Proof state:** `KERNEL_VERIFIED_AXIOM_FREE`

## Position In Derivation

P002 is the proof-certification child of `006 · C018`. Its hard mathematical input is the C003 provenance-address grammar, while its Lean proof module imports the C018 owner module in the permitted proof-to-core direction. The DAG certification edge points from P002 to C018; the Lean import points from `CNNAProofsP002` to `CNNA`.

P002 has one static responsibility:

> Prove that the C018 breadth-first/lexicographic relation is a strict total order on provenance addresses and induces a strict total order on open-slot selected children modulo extensional equality of the selected child address.

The node does not own state-dependent least-open selection. C004 owns least-open existence and uniqueness after C005 introduces the born prefix and unsaturation predicate.

## Formal Statement

Let `BirthBefore` be the C018 order on provenance addresses. The public closure packages:

<!-- CNNA-EXTREF-BEGIN EXT-USE-P002-WORDS-SUPP -->
**EXT-REF-WORDS-001 — established method context.** M. Lothaire, *Combinatorics on Words*, 2 ed., Cambridge Mathematical Library, Cambridge University Press (1997). ISBN `9780521599245`. DOI: `10.1017/CBO9780511566097`. Exact location: Ch. 1, finite words and lexicographic order. Context: Standard finite-word lexicographic context for the P002 static order theorem. Formal status: `CONTEXT_ONLY_INTERNAL_KERNEL_VERIFIED`
<!-- CNNA-EXTREF-END EXT-USE-P002-WORDS-SUPP -->

1. `¬ BirthBefore a a`;
2. `BirthBefore a b -> BirthBefore b c -> BirthBefore a c`;
3. asymmetry;
4. trichotomy `a < b ∨ a = b ∨ b < a`;
5. comparison of distinct addresses.

For C018 `OpenBirthSlot` records it packages irreflexivity, transitivity, and asymmetry of `OpenSlotBefore`, together with the extensional trichotomy

\[
 s <_{slot} t
 \;\lor\;
 \operatorname{child}(s)=\operatorname{child}(t)
 \;\lor\;
 t <_{slot} s.
\]

For a predicate `Q` on slot records,

\[
 \operatorname{IsMinimalSelectedChild}(Q,s)
 \iff Q(s)\land\forall t\,[Q(t)\Rightarrow\neg(t<_{slot}s)].
\]

The uniqueness theorem concludes equality of the selected child addresses of any two minimal witnesses.

## Hypotheses

The order closure quantifies only over:

- a C003 branching parameter and provenance addresses;
- a C018 canonical schedule;
- C018 open-slot records;
- an arbitrary predicate on those records for the minimality theorem.

No `ResponseCapableState`, born prefix, unsaturation proof, numerical response, or Python execution is a P002 hypothesis.

## Introduction Reason

C018 defines and proves the order primitives. P002 exposes their reusable proof contract without enlarging C018's core API and without importing later state layers. This gives downstream termination proofs one named certification boundary while preserving the package direction `CNNAProofsP002 -> CNNA`.

## Proof Strategy

1. Construct the address fields directly from C018 `birthBefore_*` theorems.
2. Construct the slot fields directly from C018 `openSlotBefore_*` theorems.
3. Derive extensional slot trichotomy by applying address trichotomy to the two selected child addresses.
4. For minimal-witness uniqueness, split on equality of selected children.
5. Under inequality, use C018 total comparison of distinct selected children.
6. Each comparison direction contradicts one of the two minimality hypotheses.
7. Export the closure through a stable proposition-valued public contract.

## Lemma Chain

```text
C018.BirthBefore
  -> birthBefore_irrefl
  -> birthBefore_trans
  -> birthBefore_asymm
  -> birthBefore_trichotomy
  -> birthBefore_total_of_ne

C018.OpenSlotBefore
  -> openSlotBefore_irrefl
  -> openSlotBefore_trans
  -> openSlotBefore_asymm
  -> openSlotBefore_total_of_distinct_children

P002
  -> CanonicalScheduleStrictTotalOrderClosure
  -> canonicalScheduleStrictTotalOrderClosure
  -> IsMinimalSelectedChild
  -> minimalSelectedChild_unique
  -> CanonicalScheduleStrictTotalOrderContract
  -> canonicalScheduleStrictTotalOrderContract
```

## Formal Realization

The proof source is:

`derivation/code/lean/proofs/src/CNNAProofs/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S01_PrimitiveInputsGrammarAndEventOrder/S06_C018_CanonicalBfsLexicographicProvenanceBirthSchedule/Proofs/S01_P002_CanonicalScheduleStrictTotalOrderClosure.lean`

The independent root `proofs/src/CNNAProofsP002.lean` exports exactly this module.

<!-- CNNA-EXTREF-BEGIN EXT-USE-P002-LEAN-LISTLEX-SUPP -->
**EXT-REF-LEAN-007 — formalization guidance.** The Lean 4 Development Team, *Lean core module: Init.Data.List.Basic (List.Lex)*, Lean FRO, LLC (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://github.com/leanprover/lean4/blob/v4.31.0/src/Init/Data/List/Basic.lean`; accessed 2026-08-08. Exact location: List.Lex and decidableLex, Init/Data/List/Basic.lean at v4.31.0. Context: Pins the exact Lean Core API underlying C018 address lexicography. Formal status: `GUIDANCE_ONLY_KERNEL_VERIFIED_NO_CORE_MATHLIB`
<!-- CNNA-EXTREF-END EXT-USE-P002-LEAN-LISTLEX-SUPP --> The separate library target prevents changes to the exact source sets already bound to the P001 and M003/M004 kernel evidence.

There is no P002 Python module. Static order closure is a theorem packaging task, not a second implementation of the C018 schedule.

## Counterexamples Or Necessity Checks

1. **Remove transitivity:** two locally comparable steps no longer justify an earlier-than conclusion across a chain.
2. **Remove total comparison:** two distinct minimal selected children may remain incomparable, so uniqueness does not follow.
3. **Demand record equality:** proof-bearing slot records may encode the same selected child without being definitionally identical; the correct result is extensional child equality.
4. **Add least-open state selection:** the statement would require C005/C004 and create a backward dependency at node 007.
5. **Add Python agreement:** this would conflate a static theorem facade with the later executable selector owned by C004.

## Axiom Profile

The 2026-08-08 Lean 4.31.0 audit enumerates all six public declarations with `#print axioms`. Every declaration has the empty profile `[]`: no `propext`, no `Classical.choice`, no `Quot.sound`, and no project-local axiom is observed transitively. This is stronger than merely passing the project allow-list.

## Verification

- Toolchain: `leanprover/lean4:v4.31.0`.
- mathlib in the proof package: `v4.31.0`, commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; the CNNA Core remains mathlib-free.
- Core build: 26 jobs.
- Proof-package build: 8599 jobs.
- `P002_CURRENT_PROOF_AXIOM_AUDIT PASS`.
- `p002_static_order_closure_olean: true`.
- retained P001 and M003/M004 source-hash checks: `true`.
- `FULL_PACKAGE_BOUNDARY_AUDIT PASS`.
- Build evidence: `derivation/code/lean/audit/evidence/USER_LOCAL_P002_FULL_BUILD_20260808.json`.
- Transcript SHA-256: `f4e55408d79041f2068fded77ca791196828e478b6a12b4f13decec2729131b1`.

## Result

The contract and all six public declarations are kernel-verified for the bound source hashes. The dedicated P002 axiom audit is fully empty (`6/6` axiom-free), and the full package-boundary audit passes without warnings or errors.

## Remaining Limits

P002 does not prove:

- existence of an un-born address in an unsaturated C005 state;
- uniqueness of the C004 next-open address;
- equality with the Python positional selector;
- termination of the full finite birth process.

The first three are C004 responsibilities. Full finite schedule exhaustivity and termination belong to P004.

## Downstream Handoff

`E141: P002 -> C018` now records the kernel-verified static-order certification of the owner closure. `E151: P002 -> P004` supplies the static order interface used by finite schedule exhaustivity. The obsolete `P002 -> P003` edge is absent because P003 consumes C018/C004 directly.

## Code Line Register

Path: `derivation/code/lean/proofs/src/CNNAProofs/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S01_PrimitiveInputsGrammarAndEventOrder/S06_C018_CanonicalBfsLexicographicProvenanceBirthSchedule/Proofs/S01_P002_CanonicalScheduleStrictTotalOrderClosure.lean`

- `CanonicalScheduleStrictTotalOrderClosure`, structure, lines 19–65.
- `canonicalScheduleStrictTotalOrderClosure`, theorem, lines 69–99.
- `IsMinimalSelectedChild`, definition, lines 104–109.
- `minimalSelectedChild_unique`, theorem, lines 115–131.
- `CanonicalScheduleStrictTotalOrderContract`, definition, lines 134–135.
- `canonicalScheduleStrictTotalOrderContract`, theorem, lines 138–140.

## Infobox — Order Before Dynamics

P002 demonstrates a deliberate separation: the canonical order of admissible provenance continuations is closed first; only later does C004 use an evolving born-prefix state to determine which admissible continuation is actually the least currently open slot. Thus kinematic provenance order is not conflated with state-dependent dynamics.
