# 009 · A001 — Genesis seed ★

**Canonical node label:** `009 · A001`  
**Semantic ID:** `A001`  
**Current section path:** `1.2.2`  
**Documentation tier:** `D0`  
**Documentation state:** `COMPLETE_V2`

## Position In Derivation

A001 is an auxiliary graph root with no hard predecessor. It is placed after C004A in the reading order because C013 is the first construction that needs an explicit bootstrap argument. This placement does not mean that A001 is derived from C004A. Verified edge `E006: A001 -> C013` is its only direct hard handoff in the bootstrap block.

## Definition Or Statement

The seed carrier is the singleton set

\[
\mathcal S_\star=\{\star\}.
\]

The element $\star$ has no numerical value and no address, parent, child, relation, conductance, response, birth time, event index, geometry or dynamical field. A001 is an explicit constructor token, not a free CNNA model input and not a physical initial state.

## Introduction Reason

The first non-root birth is exceptional: before the first relation exists there is no nontrivial response network from which a recurrent birth law can be evaluated. An explicit bootstrap argument makes that exceptional constructor visible instead of hiding it in a null value or an undocumented special case. The argument must be information-free so that it cannot smuggle a third parameter into the derivation.

## Construction Or Encoding

Python uses a frozen, slotted, zero-field dataclass `GenesisSeed` and the canonical instance `GENESIS_SEED`. Python can allocate distinct object identities, but every instance has the same empty dataclass value and therefore compares equal.

Lean uses the one-constructor inductive type

```text
GenesisSeed.star
```

with `GenesisSeed.canonical := .star`. The theorem `eqCanonical` proves by constructor elimination that every value equals the canonical token. Python and Lean therefore implement the same singleton carrier while using language-appropriate object mechanics.

## Boundary Case Or Countercheck

The node-local Python test checks two independent boundaries:

1. `dataclasses.fields(GenesisSeed) == ()`, so no hidden payload exists;
2. the canonical token lacks every downstream result-like attribute listed by the test.

A type with one constructor but a payload field would fail the A001 contract. Likewise, a numerical sentinel such as `0` would be semantically weaker because it belongs to a larger carrier and invites accidental arithmetic use. The singleton type prevents both failure modes.

## Result

A001 closes the existence of exactly one explicit bootstrap token and proves at the type level that the token contains no choice. It does not prove that a downstream constructor ignores the token.

## Downstream Handoff

- `E006: A001 -> C013` is `ACTIVE_VERIFIED` and supplies the information-free token.
- T001 later proves equality of the generated first-birth states for arbitrary explicit seed arguments.

## Code Anchors
### Python source

**Path:** `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/s02_a001__genesis_seed_star.py`  
**Source SHA-256:** `3cdeb86555d9ed8468a0b1a0d27d0922fe4a6694458648312c0bd20934614f5f`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `GenesisSeed` | `CLASS` | 14-15 | singleton carrier / zero-field runtime carrier |

### Python test

**Path:** `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/test_s02_a001__genesis_seed_star.py`  
**Source SHA-256:** `7f36399821677bd576ae63796e554cdfc987b846c49dd48a496feed940eca7e9`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `TestGenesisSeed` | `CLASS` | 13-24 | payload and singleton-value counterchecks |

### Lean core source

**Path:** `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S02_BootstrapOfTheFirstRelation/S02_A001_GenesisSeedStar.lean`  
**Source SHA-256:** `955dc9eafbdeea80ad1eabf998a0dcf576bfa632d2ae5e7a9e77ccb467cfb0d0`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `GenesisSeed` | `INDUCTIVE` | 12-17 | singleton carrier / zero-field runtime carrier |
| `canonical` | `DEF` | 18-20 | canonical singleton token |
| `eqCanonical` | `THEOREM` | 21-27 | universal singleton equality theorem |

**Registered anchors for A001:** 5. Every path, line range and source hash is also present in `derivation/registry/documentation/CODE_ANCHORS.tsv`.
