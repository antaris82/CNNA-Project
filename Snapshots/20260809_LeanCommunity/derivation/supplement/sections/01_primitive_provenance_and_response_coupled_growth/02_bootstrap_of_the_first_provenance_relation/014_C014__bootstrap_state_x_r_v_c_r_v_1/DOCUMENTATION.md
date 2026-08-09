# 014 · C014 — Bootstrap state X₁

**Canonical node label:** `014 · C014`  
**Semantic ID:** `C014`  
**Current section path:** `1.2.7`  
**Documentation tier:** `D1`  
**Documentation state:** `COMPLETE_V2`

## Position In Derivation

C014 is the terminal construction of the exceptional-bootstrap group. It has three verified hard predecessors:

- `E011: C013 -> C014`, the concrete first birth;
- `E012: T001 -> C014`, seed-neutrality;
- `E013: M005 -> C014`, unit-representative independence.

Its verified outgoing edge `E014: C014 -> C005` supplies the base case for recurrent states.


<!-- CNNA-ARCHITECTURE-BEGIN C014 -->
## CNNA Architecture Role

C014 is the first response-capable CNNA state. It packages the weighted root/newborn net from which later nodes can form retained/complement cuts, eliminate interiors, and couple effective response back into growth. C014 is only the base carrier; it does not yet perform those operations.
<!-- CNNA-ARCHITECTURE-END C014 -->

## Mathematical Contract

The state $X_1$ contains

\[
V_1=\{\varepsilon,(0)\},
\quad
\mathcal R_1=((\varepsilon,(0)),((0),\varepsilon)),
\quad
\mathcal C_1=(1,1).
\]

The implementation represents this information minimally by storing the C013 birth once and deriving the displayed components by projection. The set notation is a mathematical view, not a claim that the runtime object contains a redundant set field.

## Introduction Reason

C013 creates the exceptional relation, but the recurrent layer needs a named state object that packages the relation and carries the two no-hidden-input certificates. C014 marks the exact transition from initialization to the domain on which later response constructions can act.

## Explicit Construction

Python defines

```text
BootstrapState(birth : FirstNonRootBirth)
```

with projections `root`, `newborn`, `directed_relations` and `directed_conductances`. `build_bootstrap_state` is the one-field constructor.

Lean defines the same one-field structure and constructor. It then provides:

- root and newborn projections;
- the inherited unit-pair theorem;
- `fromSeed_seedNeutral`, obtained by applying `congrArg build` to T001;
- `directedConductancesRat`, the rational lift of the actual stored pair;
- `directedConductancesRat_eq_n001_pair`;
- `conductanceUnit_isRepresentativeOnly`, which applies M005 to each orientation.

## Invariants

1. the carrier view contains exactly root and first newborn;
2. the relation contains both provenance-parent orientations;
3. both stored conductances are one;
4. no seed field is present;
5. no variable unit field is present;
6. the comparison scale used by M005 produces no alternative `BootstrapState` value.

## Canonicity Or Uniqueness

For each C013 birth there is exactly the transparent one-field wrapper produced by `build`. C014 does not prove uniqueness of C013 itself; it inherits C013's data. The T001 theorem proves independence from explicit seed arguments, and M005 proves representative invariance of the normalized conductance coordinate. Together these exclude the two intended hidden bootstrap choices.

## Boundary Cases

- $L=0$: C013 cannot be constructed, hence neither can C014.
- $L\ge1$: C014 is available once the C013 birth is supplied.
- The phrase “response-capable” means a nontrivial weighted relation exists. No Schur complement, DtN response, steering scalar, geometry, event time or recurrent update is evaluated here.

## Python Lean Cross Layer

Python stores only the birth and exposes executable projections. Lean stores the same birth and adds proof theorems around it. These theorems do not enlarge the runtime payload. The rational lift in Lean is a proof-side view of the natural-number pair used for M005; Python's C014 module does not duplicate that proof because the exact scalar theorem is tested in M005's module.

## Countercheck

The Python test constructs the complete chain from grammar through C014, checks root, newborn, both relations and both conductances, and audits the dataclass fields as exactly `("birth",)`. The constructor's `__post_init__` rejects a value of any other exact type. These checks exclude duplicated state components and hidden certificate variables.

## Result

C014 closes the first response-capable weighted provenance state and the exceptional initialization section. The D6 registry synchronization marks its obsolete blocked-obligation row as `CLOSED_VERIFIED`; no mathematical source is changed.

## Downstream Handoff

- `E014: C014 -> C005` is `ACTIVE_VERIFIED` and supplies the recurrent base case.
- `E077: C014 -> C019` and `E153: C014 -> P005` remain `PLANNED_BLOCKED`; they require the later recurrent iteration and proof closure.

## Code Anchors
### Python source

**Path:** `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/s07_c014__bootstrap_state_x1_r_v1_c_r_v1_1.py`  
**Source SHA-256:** `3b2115e677362fae2c1205e74b37f020a93f2a069e31a560484d899dd38d6f28`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `BootstrapState` | `CLASS` | 23-46 | minimal one-field bootstrap-state carrier |
| `build_bootstrap_state` | `FUNCTION` | 49-51 | executable wrapper constructor |

### Python test

**Path:** `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/test_s07_c014__bootstrap_state_x1_r_v1_c_r_v1_1.py`  
**Source SHA-256:** `efa56d83c92ded843c844b52f9271816a58bf9f333a8942c109d1103334b8355`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `TestBootstrapState` | `CLASS` | 18-30 | full state and payload-minimality test |

### Lean core source

**Path:** `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S02_BootstrapOfTheFirstRelation/S07_C014_BootstrapStateX1RV1CRV11.lean`  
**Source SHA-256:** `6894fdaf9854f4d7251d828bf756a54aa2730d94fe84f733acb9d829c57e65f5`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `BootstrapState` | `STRUCTURE` | 23-28 | minimal one-field bootstrap-state carrier |
| `build` | `DEF` | 29-32 | formal wrapper constructor |
| `rootAddress` | `DEF` | 33-36 | root projection |
| `newbornAddress` | `DEF` | 37-40 | newborn projection |
| `directedConductances_eq_unit_pair` | `THEOREM` | 41-45 | inherited unit-pair theorem |
| `fromSeed_seedNeutral` | `THEOREM` | 46-55 | T001 certificate lifted to X1 |
| `directedConductancesRat` | `DEF` | 56-60 | rational lift of actual pair |
| `directedConductancesRat_eq_n001_pair` | `THEOREM` | 61-74 | actual pair/N001 identity theorem |
| `conductanceUnit_isRepresentativeOnly` | `THEOREM` | 75-99 | M005 applied to both stored orientations |

**Registered anchors for C014:** 12. Every path, line range and source hash is also present in `derivation/registry/documentation/CODE_ANCHORS.tsv`.
