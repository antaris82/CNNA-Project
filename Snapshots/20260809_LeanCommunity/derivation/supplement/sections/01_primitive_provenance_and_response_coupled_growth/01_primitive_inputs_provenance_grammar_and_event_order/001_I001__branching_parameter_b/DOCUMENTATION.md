# 001 · I001 — Branching parameter b

**Canonical node label:** `001 · I001`  
**Semantic ID:** `I001`  
**Current section path:** `1.1.1`  
**Documentation tier:** `D0`  
**Node role:** free structural input  
**Verification status:** Python tests reproduced; Lean source kernel-built in the current prefix-free 26-core-job package.

## Position in the derivation

`I001` is the first node in the canonical derivation order and one of the three visible origin nodes. It has no incoming edge. Its local responsibility is limited to the branching multiplicity that will later parameterize the address grammar. It neither depends on the empty carrier `C001` nor creates any carrier state.

This separation is intentional: a free parameter and an initial object may coexist at the origin without one being derived from the other. The single DAG records both as inputs to later constructions.

## Definition or statement

The scientific contract is the subtype

\[
\mathcal B = \{b\in\mathbb N \mid 2\le b\}.
\]

A CNNA finite-provenance instance supplies an explicit element `b` of this set. The node asserts no default value and no probability distribution over admissible values.

The lower bound is part of the declared model family. In particular, the documentation does **not** infer that `b = 1` is inconsistent in mathematics; it states only that the unary case lies outside the admissible domain of `I001` and may be considered separately as a comparison or control.

## Introduction reason

The child-slot alphabet used by `C003` cannot be defined before its cardinality is known. `I001` is therefore introduced at the origin and handed to `C003` through edge `E001` (`parameterizes_branching`). Keeping the lower-bound proof at this boundary prevents downstream modules from silently assuming `b ≥ 2` as an undocumented side condition.

## Construction or encoding

### Mathematical representation

The abstract value is a natural number paired with evidence of `2 ≤ b`.

### Python representation

`BranchingParameter` is a frozen, slotted dataclass with one stored field, `value`. Construction checks:

1. `type(value) is int`;
2. `value >= 2`.

The use of exact built-in type equality is deliberate. Python implements `bool` as a subclass of `int`; accepting `isinstance(True, int)` would allow a logical flag to enter as the numerical branching value `1`.

### Lean representation

Lean uses

```lean
structure BranchingParameter where
  value : Nat
  ge_two : 2 ≤ value
```

The proposition is stored in the value itself. `lowerBound` is an explicit projection theorem and `mk_value` exposes the constructor equation at the module boundary. There is no default inhabitant and no local axiom declaration.

### Cross-layer correspondence

Python and Lean implement the same admissible numerical values but enforce validity differently:

- Python permits attempted invalid construction and rejects it at runtime;
- Lean requires a proof argument before the invalid value can be constructed.

This is semantic equivalence of the accepted domain, not syntactic identity of the implementations.

## Boundary case or countercheck

The node-local counterchecks are:

- `b = 2` is admitted as the lower boundary;
- larger integers are admitted without a fixed upper bound;
- `b ∈ {-3,-1,0,1}` is rejected;
- `True`, `False`, `2.0`, `"2"`, and `None` are rejected by the Python type boundary;
- in Lean, any claimed inhabitant automatically carries `2 ≤ value`, so a value below two cannot be produced without inconsistency in the ambient logic.

These tests establish the input boundary only. They do not prove properties of the later `b`-ary carrier, schedule, or growth law.

## Result

`I001` closes the following narrow statement:

> One explicit branching multiplicity `b` is available, and every accepted representation satisfies exactly `b ∈ ℕ` and `b ≥ 2`.

No geometry, node, relation, event ordering, conductance, response, or dynamics is introduced. The node is frozen as a verified input contract; its documentation is now complete under schema v2.

## Downstream handoff

- `E001: I001 → C003` supplies the branching multiplicity for the finite slot alphabet and address grammar.
- `E147: I001 → P004` supplies the same bound to the later proof that the bounded canonical schedule enumerates the finite carrier.

`E147` is proof support, not an additional definition of `b`.

## Code anchors

All line intervals refer to the current source hashes. Symbol plus source SHA-256 is the stable identity; line numbers are reading aids.

### Python source

- Path: `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s01_primitive_inputs_grammar_and_event_order/s01_i001__branching_parameter_b.py`
- Symbol: `BranchingParameter`
- Kind: class
- Lines: 20–46
- SHA-256: `504e678397db5f6f969a5c69a6da9a2a36f34308201b0629b558331b453c1f69`

### Python counterchecks

- Path: `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s01_primitive_inputs_grammar_and_event_order/test_s01_i001__branching_parameter_b.py`
- Symbol: `TestBranchingParameter`
- Kind: test class
- Lines: 12–33
- SHA-256: `189ec3b317faa474ece1d2105eaeb347fee053f210fe0bd24c5e8d10106c7d9c`
- Covered cases: lower boundary, larger values, values below two, non-integer and Boolean rejection.

### Lean source

Path: `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S01_PrimitiveInputsGrammarAndEventOrder/S01_I001_BranchingParameterB.lean`  
SHA-256: `b826f2eca8aa535447d1c5c0090989d838ea30fac381e4c3c925b98c2bd96c96`

- `BranchingParameter`, structure, lines 17–23: value and lower-bound proof.
- `lowerBound`, theorem, lines 24–27: explicit projection `2 ≤ b.value`.
- `mk_value`, theorem, lines 28–34: definitional constructor equation.
