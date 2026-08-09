# 012 · T001 — Seed-neutrality theorem for first birth

**Canonical node label:** `012 · T001`  
**Semantic ID:** `T001`  
**Current section path:** `1.2.5`  
**Documentation tier:** `D2`  
**Documentation state:** `COMPLETE_V2`

## Position In Derivation

T001 follows C013 through verified edge `E009`. A001 proves only that the seed carrier is singleton-valued; C013 shows that the seed is not stored. T001 is the theorem node that turns this design into an explicit equality statement and passes the certificate to C014 through `E012`.

## Formal Statement

For any C004A slot `slot`, seeds `eta etaPrime : GenesisSeed`, N001 normalization `normalization`, and cutoff proof `h`, the current Lean theorem states

```text
firstWeightedStateFromSeed slot eta normalization h =
  firstWeightedStateFromSeed slot etaPrime normalization h
∧ directedConductances (...) = (1, 1)
```

Equivalently,

\[
B(slot,\eta,N,h)=B(slot,\eta',N,h)
\quad\land\quad
\mathcal C(B(slot,\eta,N,h))=(1,1).
\]

## Hypotheses

- one fixed structural C004A slot;
- two arbitrary explicit A001 seed values;
- one fixed N001 normalization;
- admission of the slot into the finite cutoff.

No response, geometry, time or recurrent state is assumed.

## Introduction Reason

The seed is needed to expose the exceptional bootstrap boundary, but the model must not inherit a hidden state variable from it. Keeping T001 separate from A001 and C013 makes the no-information claim falsifiable: a later modification that stores or uses the seed would break the theorem rather than silently changing the meaning of the token.

## Proof Strategy

`firstWeightedStateFromSeed` is a transparent wrapper around `FirstNonRootBirth.build`. The build function ignores its seed argument when creating the record. Therefore both generated states reduce to the same term and the equality branch is proved by `rfl`. The conductance branch invokes C013's `directedConductances_eq_unit_pair`.

## Lemma Chain

```text
C013.FirstNonRootBirth.build
  -> firstWeightedStateFromSeed
  -> definitional equality under eta / etaPrime

C013.directedConductances_eq_unit_pair
  -> second conjunct of seedNeutralityFirstBirth
```

A001's `eqCanonical` is available but is not used. This matters: the current theorem follows from structural seed erasure, not merely from rewriting all seeds to the unique constructor.

## Formal Realization

Python's `first_weighted_state_from_seed` calls the same C013 builder. The test creates two distinct `GenesisSeed()` objects, verifies distinct identity, and then checks equality of the generated records and the pair `(1,1)`.

Lean quantifies over arbitrary seed values and proves the conjunction in the mathlib-free core. The theorem is kernel-checkable with the package's pinned Lean version and depends only on the imported C013 definitions and theorem.

## Counterexamples Or Necessity Checks

- Adding a `seed` field to `FirstNonRootBirth` would destroy the direct `rfl` proof unless equality were separately quotiented or rewritten.
- Using the seed to choose a child address or conductance would invalidate the theorem even though A001 currently has one constructor; it would reveal a meaningless but structurally present dependency.
- Removing the common cutoff hypothesis would make the two terms ill-typed, because C013 is not defined outside the admitted first slot.

## Axiom Profile

The theorem body uses `rfl` and an exact imported theorem. The source is in the dependency-free core package and contains no project `axiom`, `sorry`, `admit`, `opaque`, `unsafe` or `partial` declaration; its listed source hash is the verified current hash.

## Result

T001 proves exact state equality, not merely equality of selected observables. The first birth leaves no seed state variable behind.

## Remaining Limits

The theorem is restricted to the exceptional first birth. It says nothing about hypothetical seed arguments in later recurrent steps, and it does not prove M005's unit-independence statement.

## Downstream Handoff

`E012: T001 -> C014` is `ACTIVE_VERIFIED` and certifies the seed-neutrality component of the packaged bootstrap state.

## Code Line Register
### Python source

**Path:** `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/s05_t001__seed_neutrality_theorem_for_first_birth.py`  
**Source SHA-256:** `0fd2df73db6f59d70b83d22c58fa8089b418061e7ecfe4c8d4f1c167cd3beed4`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `first_weighted_state_from_seed` | `FUNCTION` | 15-21 | executable seed-indexed wrapper |

### Python test

**Path:** `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/test_s05_t001__seed_neutrality_theorem_for_first_birth.py`  
**Source SHA-256:** `24a74c3e5fc36b2d4cae7e8d1c517598e6d78556c9ed0e5645512254f82863da`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `TestSeedNeutralityFirstBirth` | `CLASS` | 16-27 | distinct-instance equality test |

### Lean core source

**Path:** `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S02_BootstrapOfTheFirstRelation/S05_T001_SeedNeutralityTheoremForFirstBirth.lean`  
**Source SHA-256:** `e2da5d1e066d13c176bc9e05a0c3c892ee60c8169c7ddb3d050428f4e675b705`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `firstWeightedStateFromSeed` | `DEF` | 15-26 | formal seed-indexed wrapper |
| `seedNeutralityFirstBirth` | `THEOREM` | 27-41 | universal state equality and conductance theorem |

**Registered anchors for T001:** 4. Every path, line range and source hash is also present in `derivation/registry/documentation/CODE_ANCHORS.tsv`.
