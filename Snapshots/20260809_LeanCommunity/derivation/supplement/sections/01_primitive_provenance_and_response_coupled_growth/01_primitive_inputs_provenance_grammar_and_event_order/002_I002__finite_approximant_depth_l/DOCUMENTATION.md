# 002 · I002 — Finite approximant depth L

**Canonical node label:** `002 · I002`  
**Semantic ID:** `I002`  
**Current section path:** `1.1.2`  
**Documentation tier:** `D0`  
**Node role:** free finite-cutoff input  
**Verification status:** Python tests reproduced; Lean source kernel-built in the current prefix-free 26-core-job package.

## Position in the derivation

`I002` is the second canonical node and a visible origin input. It has no incoming edge. It supplies a finite terminal depth to later constructions but does not itself construct an address, carrier, root, or schedule.

Its independence from `I001` is exact: branching multiplicity and finite depth are separate coordinates of the finite approximant. Neither determines the other.

## Definition or statement

The contract is

\[
L\in\mathbb N_0.
\]

Equivalently, `L` is a nonnegative integer. The value is supplied explicitly, `L = 0` is admissible, and no infinity, `None`, negative value, or special unbounded sentinel belongs to the domain.

This node does not identify `L` with physical time, graph distance, or a continuum coordinate. It is a finite cutoff on provenance-address depth. The interpretation of `L = 0` as a root-only approximant requires the subsequent root and grammar nodes; at `I002` alone it is only the lower endpoint of the input domain.

## Introduction reason

The grammar `C003` must know which address depths are admitted, and the later completion node `C019` must know where finite construction terminates. Therefore `I002` is fixed at the origin and transmitted through `E002` and `E081`. Stating finiteness here prevents an implicit infinity convention from entering downstream code.

## Construction or encoding

### Mathematical representation

The abstract domain is `ℕ₀`; no additional predicate is required.

### Python representation

`FiniteApproximantDepth` is a frozen, slotted dataclass with one `value` field. Its constructor checks exact built-in-integer type and the lower bound `value >= 0`. The value is returned without implicit coercion by `to_int`.

### Lean representation

Lean uses a one-field structure:

```lean
structure FiniteApproximantDepth where
  value : Nat
```

No proof field is necessary because `Nat` already enforces nonnegativity. `mk_value` records the constructor equation, and `zeroAdmissible` proves the existence of an ordinary inhabitant with value zero.

### Cross-layer correspondence

The accepted mathematical values agree exactly:

- Python built-in integers at least zero;
- Lean natural numbers.

Python performs a runtime rejection of invalid external values. Lean excludes them by type. The Python rejection of Boolean values is an implementation-boundary refinement needed because Python's class hierarchy differs from Lean's type separation.

## Boundary case or countercheck

The node-local checks establish:

- `L = 0` is admitted and round-trips exactly;
- arbitrary positive integers are admitted;
- negative integers are rejected;
- floating-point zero, strings, `None`, and Boolean values are rejected.

The countercheck distinguishes an ordinary zero-depth value from an infinity or missing-value sentinel. No theorem in this node proves convergence as `L → ∞`; finite-to-infinite completion remains a separate downstream obligation.

## Result

`I002` closes the following statement:

> One explicit finite approximant depth is available, with accepted values exactly `ℕ₀`, including zero and excluding every non-finite sentinel.

The node introduces no temporal, geometric, or dynamical interpretation. Its documentation is complete under schema v2.

## Downstream handoff

- `E002: I002 → C003` bounds the admitted provenance addresses.
- `E081: I002 → C019` sets the finite completion depth.
- `E148: I002 → P004` provides the finite cutoff to the later enumeration and termination proof.

These edges reuse the same input; they do not define different meanings of `L`.

## Code anchors

### Python source

- Path: `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s01_primitive_inputs_grammar_and_event_order/s02_i002__finite_approximant_depth_l.py`
- Symbol: `FiniteApproximantDepth`
- Kind: class
- Lines: 20–46
- SHA-256: `f0f5fefe55d90835e8deead733579848d547b6b6df7e40b6491a1f578b64b326`

### Python counterchecks

- Path: `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s01_primitive_inputs_grammar_and_event_order/test_s02_i002__finite_approximant_depth_l.py`
- Symbol: `TestFiniteApproximantDepth`
- Kind: test class
- Lines: 12–33
- SHA-256: `8836bb6a9740dc29d66c65ea121d3e3dc2445764b6f28f61e8928b5b6f70772b`
- Covered cases: zero, positive values, negative rejection, non-integer and Boolean rejection.

### Lean source

Path: `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S01_PrimitiveInputsGrammarAndEventOrder/S02_I002_FiniteApproximantDepthL.lean`  
SHA-256: `ae23109e12622fc6494aad18bc056bf59206d18199288c101520d9c58f5b99e8`

- `FiniteApproximantDepth`, structure, lines 18–23: natural-valued finite cutoff.
- `mk_value`, theorem, lines 24–28: definitional constructor equation.
- `zeroAdmissible`, theorem, lines 29–34: zero is a genuine admissible value.
