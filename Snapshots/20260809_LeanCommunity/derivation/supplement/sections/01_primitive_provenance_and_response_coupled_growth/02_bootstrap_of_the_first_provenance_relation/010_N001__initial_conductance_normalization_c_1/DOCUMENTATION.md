# 010 · N001 — Initial conductance normalization C★=1

**Canonical node label:** `010 · N001`  
**Semantic ID:** `N001`  
**Current section path:** `1.2.3`  
**Documentation tier:** `D0`  
**Documentation state:** `COMPLETE_V2`

## Position In Derivation

N001 is a fixed-normalization graph root. It is introduced immediately before C013 because the first directed relation requires an initial conductance representative. It is independent of A001 and C004A. Its hard outgoing edges are `E008: N001 -> C013` and `E010: N001 -> M005`.

## Definition Or Statement

N001 fixes the dimensionless bootstrap representative

\[
C_\star=1
\]

and the initial directed pair

\[
(C_{r\to v_1},C_{v_1\to r})=(1,1).
\]

This is a normalization convention and not a free scalar parameter. N001 owns neither endpoint, the relation, the birth, nor the later proof that another positive unit is equivalent.

## Introduction Reason

A weighted root-child relation must enter the recurrent development with a concrete representative. Choosing one removes an otherwise arbitrary common scale at the bootstrap boundary. The nontrivial justification that this choice does not add physical information must remain separate: N001 defines the representative; M005 proves the comparison theorem.

## Construction Or Encoding

Python stores no payload in `InitialConductanceNormalization`. The properties `value` and `directed_values` return the module constant `C_STAR=1` and `(1,1)`.

Lean uses a one-constructor inductive type. `value` is definitionally `1 : Nat`; `directedValues` duplicates that value; `directedValues_eq_unit_pair` proves the pair is exactly `(1,1)` by reflexivity.

The local `Nat` carrier is part of the bootstrap representation only. M005 later embeds this numeral into `Rat`; later effective conductance carriers are not fixed by the present type choice.

## Boundary Case Or Countercheck

Python rejects `InitialConductanceNormalization(2)`, demonstrating that `2` is not an alternative state of this node. The field audit excludes endpoint, relation, address, event and birth payloads. The Lean type has no alternative constructor or field.

This fixedness does not imply unit-independence. Without M005, the statement “one is only a representative” would be unsupported because no alternative positive unit appears in N001's type.

## Result

N001 closes the canonical bootstrap pair `(1,1)` and only that pair.

## Downstream Handoff

- `E008: N001 -> C013` supplies the first-relation conductances.
- `E010: N001 -> M005` supplies the canonical representative whose scale class M005 analyzes.

## Code Anchors
### Python source

**Path:** `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/s03_n001__initial_conductance_normalization_c_star_1.py`  
**Source SHA-256:** `d41e916f59a9b6c8b6fbec95f10f171a2f95714838f3948ac7f75112c7c8eab0`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `InitialConductanceNormalization` | `CLASS` | 23-34 | fixed zero-payload normalization carrier |

### Python test

**Path:** `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/test_s03_n001__initial_conductance_normalization_c_star_1.py`  
**Source SHA-256:** `fde5d880a23f305aed54815862fc8133bd7b209cc769a1d79048e9aa09a25327`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `TestInitialConductanceNormalization` | `CLASS` | 14-29 | unit-pair and no-free-value counterchecks |

### Lean core source

**Path:** `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S02_BootstrapOfTheFirstRelation/S03_N001_InitialConductanceNormalizationCStar1.lean`  
**Source SHA-256:** `fec821addfc248edd0352e4977b46f92693b14bcac09de7080afe6a779c22c17`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `InitialConductanceNormalization` | `INDUCTIVE` | 15-20 | fixed zero-payload normalization carrier |
| `canonical` | `DEF` | 21-23 | canonical normalization token |
| `value` | `DEF` | 24-26 | fixed scalar representative one |
| `directedValues` | `DEF` | 27-30 | two-orientation initialization |
| `directedValues_eq_unit_pair` | `THEOREM` | 31-37 | exact unit-pair theorem |

**Registered anchors for N001:** 7. Every path, line range and source hash is also present in `derivation/registry/documentation/CODE_ANCHORS.tsv`.
