# 003 · C001 — Empty carrier ∅

**Canonical node label:** `003 · C001`  
**Semantic ID:** `C001`  
**Current section path:** `1.1.3`  
**Documentation tier:** `D0`  
**Node role:** primitive initial carrier  
**Verification status:** Python tests reproduced; Lean source kernel-built in the current prefix-free 26-core-job package.

## Position in the derivation

`C001` is the third canonical node and the nonparametric initial object of the constructive chain. It appears on the same visible origin rank as `I001` and `I002`, but its role is different: it is a unique state rather than a freely selected numerical input.

There is no incoming DAG edge. The lack of an incoming edge records that the empty carrier is not generated from an earlier carrier. Its only hard outgoing edge is the root-genesis handoff to `C002`.


<!-- CNNA-ARCHITECTURE-BEGIN C001 -->
## CNNA Architecture Role

C001 is the null baseline of **ComplemeNt Net Architecture**. It contains no realized node, no relation, and no hidden complementary payload. This makes the first realization at C002 an explicit construction rather than an implicit initial condition. The statement is architectural context, not an additional theorem.
<!-- CNNA-ARCHITECTURE-END C001 -->

## Definition or statement

Let `V` be the set of present provenance nodes and `R ⊆ V × V` the present directed relations. The C001 state is

\[
X_{\varnothing}=(V_{\varnothing},R_{\varnothing}),
\qquad
V_{\varnothing}=\varnothing,
\qquad
R_{\varnothing}=\varnothing.
\]

The complete local contract has three parts:

1. a pre-root carrier value exists;
2. it contains no node;
3. it contains no relation.

The node does **not** construct the root, an address, event order, geometry, conductance, response, or hidden initialization payload.

## Introduction reason

A derivation beginning with root genesis must distinguish the state before genesis from the rooted state after genesis. Treating the former as `None`, an absent variable, or a constructorless type would erase the source object of the transition `C001 → C002`. C001 therefore supplies one explicit, payload-free state on which the next construction acts.

## Construction or encoding

### Mathematical representation

The node and relation components are both empty. The representation is unique up to equality because no local degree of freedom is present.

In the category of sets, the empty set is an initial object: for every set `A`, exactly one map `∅ → A` exists. This is an exact contextual comparison for the empty component, not a claim that the full CNNA derivation has already been formulated categorically.

### Python representation

`EmptyCarrier` is a frozen, slotted dataclass with no stored fields. It exposes:

- `nodes = ()`;
- `relations = ()`;
- `contains_node(_) = False`;
- `contains_relation(_,_) = False`.

`EMPTY_CARRIER` is the canonical executable value. Constructing another zero-field instance yields an equal value, while attempting to pass a payload raises `TypeError`.

### Lean representation

Lean uses an inhabited singleton:

```lean
inductive EmptyCarrier : Type where
  | empty
```

`canonical` names the unique constructor value. `ContainsNode` and `ContainsRelation` are defined as `False`; `noNode` and `noRelation` expose the consequences. `eqCanonical` proves that every inhabitant is the canonical state.

A constructorless inductive type would have no inhabitant and would therefore encode “no pre-root state exists,” which is not the contract. The one constructor represents uniqueness of the carrier value, not one provenance node.

### Cross-layer correspondence

Python and Lean agree on the observable state:

- one canonical zero-payload carrier value exists;
- every node-membership query is false;
- every relation-membership query is false;
- no hidden payload distinguishes alternative carriers.

The runtime and proof representations are structurally different but semantically equivalent at the contract boundary.

## Boundary case or countercheck

The counterchecks exclude four common conflations:

1. **Empty carrier versus missing object:** `EMPTY_CARRIER` is an actual value, not `None`.
2. **Empty carrier versus rooted state:** no root is present; root creation belongs to `C002`.
3. **Empty mathematical collections versus empty datatype:** Lean's carrier type is inhabited even though its node and relation predicates are empty.
4. **Unique representation versus hidden parameter:** Python has no dataclass fields or instance dictionary, and a payload argument is rejected.

The Lean theorem `eqCanonical` is the exact uniqueness check. The Python equality and field-reflection tests are executable finite checks of the same boundary.

## Result

`C001` closes the statement:

> There exists exactly one payload-free pre-root carrier representation, and it contains neither provenance nodes nor directed relations.

This result is structural only. It does not prove or assume any property of the root that will be introduced by `C002`. The documentation is complete under schema v2.

## Downstream handoff

`E003: C001 → C002` has relation `root_genesis`. The handoff transfers the canonical empty carrier to the root-genesis construction. The edge note records that this is the only node birth before any relation exists.

No other outgoing edge leaves `C001`; all later structures must pass through the rooted state or other registered descendants.

## Code anchors

### Python source

- Path: `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s01_primitive_inputs_grammar_and_event_order/s03_c001__empty_carrier_empty.py`
- Symbol: `EmptyCarrier`
- Kind: class
- Lines: 23–52
- SHA-256: `ff6f7d36a4d2290b4007d27c384d2756bb8b6e61ed5618428f5faa30383d5ccc`
- Canonical value: `EMPTY_CARRIER`, line 55.

### Python counterchecks

- Path: `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s01_primitive_inputs_grammar_and_event_order/test_s03_c001__empty_carrier_empty.py`
- Symbol: `TestEmptyCarrier`
- Kind: test class
- Lines: 14–38
- SHA-256: `873b6eef6f8400448e914409f38c16ec657f021ade4b5b70761d2c7a9349aa93`
- Covered cases: empty collections, vacuous queries, zero stored fields, semantic uniqueness, hidden-payload rejection.

### Lean source

Path: `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S01_PrimitiveInputsGrammarAndEventOrder/S03_C001_EmptyCarrierEmpty.lean`  
SHA-256: `d5e5daf9a0b04bb596666443a8c873a7a554bd35cf7f33229aab86e930595253`

- `EmptyCarrier`, inductive type, lines 21–26: inhabited singleton representation.
- `canonical`, definition, lines 27–30: canonical pre-root value.
- `ContainsNode`, definition, lines 31–34: node membership is false.
- `ContainsRelation`, definition, lines 35–39: relation membership is false.
- `noNode`, theorem, lines 40–44: no node can belong.
- `noRelation`, theorem, lines 45–49: no ordered pair can belong.
- `eqCanonical`, theorem, lines 50–56: every inhabitant is the canonical state.
