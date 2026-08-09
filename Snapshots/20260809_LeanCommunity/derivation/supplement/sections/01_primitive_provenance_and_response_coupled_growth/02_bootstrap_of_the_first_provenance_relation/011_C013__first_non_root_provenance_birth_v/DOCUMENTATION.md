# 011 · C013 — First non-root provenance birth v₁

**Canonical node label:** `011 · C013`  
**Semantic ID:** `C013`  
**Current section path:** `1.2.4`  
**Documentation tier:** `D1`  
**Documentation state:** `COMPLETE_V2`

## Position In Derivation

C013 is the first node that joins all exceptional-bootstrap inputs:

- `E007: C004A -> C013`, the structural slot $s_1$;
- `E006: A001 -> C013`, the information-free seed token;
- `E008: N001 -> C013`, the unit conductance representative.

All three edges are `ACTIVE_VERIFIED`. The construction precedes T001 and C014 because those nodes certify and package its output.


<!-- CNNA-ARCHITECTURE-BEGIN C013 -->
## CNNA Architecture Role

C013 constructs the first nontrivial **ComplemeNt Net**. The selected open slot becomes a newborn and is linked to the already realized root by the first weighted directed relation. Root and newborn are not permanent intrinsic opposites; together they form the first realized context on which later cut-relative complements can act.
<!-- CNNA-ARCHITECTURE-END C013 -->

## Mathematical Contract

For a C004A slot

\[
s_1=(\varepsilon,0,(0))
\]

with a proof or executable check that $|(0)|\le L$, and for the A001 token and N001 normalization, C013 constructs a first non-root birth $B_1$ satisfying

\[
\operatorname{root}(B_1)=\varepsilon,
\qquad
\operatorname{newborn}(B_1)=(0),
\]

\[
\operatorname{relations}(B_1)=((\varepsilon,(0)),((0),\varepsilon)),
\qquad
\operatorname{conductances}(B_1)=(1,1).
\]

The seed is an input of the constructor but not a field of the output.

## Introduction Reason

The recurrent rule cannot produce the first relation from a pre-existing response because no nontrivial weighted network exists before that relation. C013 isolates this unavoidable exceptional initialization instead of applying the later response-coupled law outside its domain.

## Explicit Construction

Python defines the immutable record

```text
FirstNonRootBirth(slot, normalization)
```

and derives the root, newborn, two directed orientations and conductance pair by projection. `build_first_non_root_birth` verifies the exact predecessor types and calls `slot.require_admitted_address()` before returning the record.

Lean defines

```text
structure FirstNonRootBirth where
  slot          : FirstProvenanceSlot
  normalization : InitialConductanceNormalization
  withinCutoff  : FirstProvenanceSlot.WithinCutoff slot
```

and `FirstNonRootBirth.build` accepts the explicit seed but does not store it. The proof of finite admission is carried in the result type.

## Invariants

The current Lean source proves:

1. `newborn_eq_first_slot`: the newborn address is exactly the C004A address;
2. `newborn_parent_root`: C003 parent reconstruction returns the root;
3. `directedConductances_eq_unit_pair`: the two orientations are `(1,1)`.

The directed relation is stored in both orientations, but this symmetry is only the bootstrap initialization. It is not a claim that all later live directed conductances remain symmetric.

## Canonicity Or Uniqueness

Given the fixed C004A slot and N001 normalization, the endpoint, relation and conductance data are definitional projections. A001 carries no information, and the generated record contains no seed field. Nevertheless, C013 deliberately does not own the theorem comparing two explicit seed-indexed constructor calls; T001 owns that equality.

No separate theorem states uniqueness among all conceivable records satisfying the displayed equations. The closed claim is the canonicity of the provided constructor and its proved projections.

## Boundary Cases

- For $L\ge1$, C004A supplies a cutoff proof and C013 is constructible.
- For $L=0$, the word $(0)$ remains structurally defined, but the Python guard rejects it and no Lean value can be built without the false cutoff proposition.
- C013 computes no response, geometry, event number or time.

## Python Lean Cross Layer

| Aspect | Python | Lean | Semantic relation |
|---|---|---|---|
| predecessor typing | exact runtime `type` checks | static types | same admissible inputs |
| cutoff | rejecting method call | proposition argument stored in result | same depth-one gate |
| seed | explicit argument, not stored | explicit argument, not stored | same erasure boundary |
| endpoints and relations | properties | definitions | same C004A projections |
| conductances | N001 property | N001 definition and theorem | same `(1,1)` pair |

The representation difference for the cutoff proof is intentional and does not create a semantic mismatch.

## Countercheck

The focused Python tests construct the complete first relation at $L=1$, verify both directed orientations and the unit pair, reject $L=0$, and audit the dataclass fields as exactly `("slot", "normalization")`. These tests would fail if the seed were retained, if the child rank were shifted, if one orientation were omitted, or if a response-dependent value entered the bootstrap.

## Result

C013 closes the exceptional first non-root birth and its initial weighted directed relation. Its registered obligation is `CLOSED_VERIFIED` and is supported by the listed source theorems.

## Downstream Handoff

- `E009: C013 -> T001` requests the explicit seed-neutrality theorem.
- `E011: C013 -> C014` supplies the concrete birth record.

Both edges are `ACTIVE_VERIFIED`.

## Code Anchors
### Python source

**Path:** `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/s04_c013__first_non_root_provenance_birth_v1.py`  
**Source SHA-256:** `02d01363b5e7746aff7358f21d65aa44c8128795f9f6e4be0ac0d4315249251f`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `FirstNonRootBirth` | `CLASS` | 23-43 | first-birth output record |
| `build_first_non_root_birth` | `FUNCTION` | 46-63 | checked executable first-birth constructor |

### Python test

**Path:** `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/test_s04_c013__first_non_root_provenance_birth_v1.py`  
**Source SHA-256:** `1a22046c8bae87bc8424c4ccc0f5d2ac2cd975e658788a2e7330ec043ded4b84`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `slot_at_depth` | `FUNCTION` | 17-19 | test fixture exposing cutoff dependence |
| `TestFirstNonRootBirth` | `CLASS` | 22-33 | endpoint, relation, conductance and L=0 tests |

### Lean core source

**Path:** `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S02_BootstrapOfTheFirstRelation/S04_C013_FirstNonRootProvenanceBirthV1.lean`  
**Source SHA-256:** `327bb483c673c175bba16bd30964f4b869a3a4d8f41d696d7f8a02fa06c9f78a`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `FirstNonRootBirth` | `STRUCTURE` | 22-29 | first-birth output record |
| `build` | `DEF` | 30-39 | typed first-birth constructor |
| `rootAddress` | `DEF` | 40-43 | root endpoint projection |
| `newbornAddress` | `DEF` | 44-47 | C004A address projection |
| `directedRelations` | `DEF` | 48-53 | two stored orientations |
| `directedConductances` | `DEF` | 54-57 | N001 pair projection |
| `newborn_eq_first_slot` | `THEOREM` | 58-62 | newborn/C004A identity theorem |
| `newborn_parent_root` | `THEOREM` | 63-69 | parent reconstruction theorem |
| `directedConductances_eq_unit_pair` | `THEOREM` | 70-77 | unit-pair theorem |

**Registered anchors for C013:** 13. Every path, line range and source hash is also present in `derivation/registry/documentation/CODE_ANCHORS.tsv`.
