# 013 · M005 — Conductance-unit normalization independence

**Canonical node label:** `013 · M005`  
**Semantic ID:** `M005`  
**Current section path:** `1.2.6`  
**Documentation tier:** `D2`  
**Documentation state:** `COMPLETE_V2`

## Position In Derivation

M005 follows N001 through verified edge `E010`. N001 fixes one representative but cannot by itself establish representative independence. M005 introduces the comparison relation and proves the positive common-rescaling theorem before C014 uses it on the actual stored bootstrap conductances.

## Formal Statement

Lean defines

\[
\operatorname{SameNormalizedResponse}(R,C,R',C')
\quad:\Longleftrightarrow\quad
RC'=R'C.
\]

The source proves:

1. for `scale > 0`,
   \[
   (R,C)\sim(scale\,R,scale\,C);
   \]
2. the rational lift of N001 is exactly one;
3. for every positive rational unit $u$ and normalized value $x$,
   \[
   (x,1)\sim(ux,u).
   \]

Python realizes the quotient interpretation as exact `Fraction(response) / Fraction(unit)` with a positive-unit guard.

## Hypotheses

- rational scalar responses and conductance units;
- a positive comparison scale for an admissible unit change;
- in the canonical-representative theorem, a positive alternative unit.

The algebraic cross-product relation itself is defined for all rationals, but its interpretation as equality of quotients requires nonzero units; the CNNA conductance convention strengthens this to positivity.

## Introduction Reason

Without M005, fixing `C★=1` would merely hide an unexamined choice inside a singleton type. The present theorem introduces an explicit family of alternative positive representatives and proves that the dimensionless normalized datum is unchanged. This makes the claim “no third physical input” falsifiable.

## Proof Strategy

The common-rescaling theorem avoids division:

\[
R(\lambda C)=(R\lambda)C=(\lambda R)C.
\]

The canonical-representative theorem first rewrites the N001 rational lift to one and then uses commutativity and the right-unit law. Exact rational arithmetic is used throughout.

## Lemma Chain

```text
InitialConductanceNormalization.value
  -> n001ConductanceUnit
  -> n001ConductanceUnit_eq_one

SameNormalizedResponse
  + Rat.mul_assoc
  + Rat.mul_comm
  -> commonPositiveRescalingPreservesNormalizedResponse

n001ConductanceUnit_eq_one
  + Rat.mul_comm
  + Rat.mul_one
  -> n001CanonicalRepresentativeForPositiveUnit
```

## Formal Realization

Python's `normalized_response` rejects a nonpositive unit and computes an exact `Fraction`. `common_positive_rescaling_preserves_normalized_response` rejects a nonpositive scale and compares the pre- and post-rescaling quotients exactly. The test includes positive integer and proper-fraction scales, positive and negative response values, and verifies that N001 normalization returns the exact response coordinate.

Lean imports only the core rational lemmas and N001. The theorem is division-free, so no inverse or regularization enters the proof. Positivity is retained as the semantic admissibility condition even though the polynomial identity does not consume it computationally.

## Counterexamples Or Necessity Checks

- `(R,C) -> (lambda R,C)` changes the quotient unless $\lambda=1$ or $R=0$.
- `(R,C) -> (R,lambda C)` likewise changes it in general.
- `lambda=0` satisfies the bare cross-product equation but destroys the unit and is rejected by Python and by the positive-scale hypothesis.
- `lambda<0` preserves an algebraic ratio but leaves the positive-conductance domain.
- Edge-dependent or orientation-dependent rescalings are not covered by the theorem.

## Axiom Profile

The Lean source is in the mathlib-free core package, uses transparent `Rat` definitions and elementary rational lemmas, and contains no project axiom or admitted proof.

## Result

N001's value one is a canonical representative of a positive rational scaling class for the scalar normalized response. The comparison variable is not a CNNA input and is not stored in the state.

## Remaining Limits

M005 does not prove homogeneity of the entire matrix-valued Schur/DtN construction and does not establish local gauge symmetry. Its exact downstream role is narrower: it supplies the fixed positive unit representative `C★=1` consumed by M003 after the C015 identity transform.

## Downstream Handoff

- `E013: M005 -> C014` is `ACTIVE_VERIFIED` and certifies the actual bootstrap conductance pair.
- `E068: M005 -> M003` is `ACTIVE_VERIFIED` and supplies the fixed unit representative used by the canonical steering scalar.

## Code Line Register
### Python source

**Path:** `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/s06_m005__conductance_unit_normalization_independence.py`  
**Source SHA-256:** `ba2e0d83204355d034d00d155442d024a8d700a91eebe92a6d55d8761bea73ba`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `normalized_response` | `FUNCTION` | 19-24 | exact positive-unit quotient |
| `n001_normalized_response` | `FUNCTION` | 27-32 | N001 representative quotient |
| `common_positive_rescaling_preserves_normalized_response` | `FUNCTION` | 35-46 | executable exact rescaling check |

### Python test

**Path:** `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/test_s06_m005__conductance_unit_normalization_independence.py`  
**Source SHA-256:** `b0da8ba116abef2a971d43861c476f0fa31d7e84bf7eaac238adf6202cc8d0aa`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `TestConductanceUnitNormalizationIndependence` | `CLASS` | 14-25 | positive rational scaling tests |

### Lean core source

**Path:** `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S02_BootstrapOfTheFirstRelation/S06_M005_ConductanceUnitNormalizationIndependence.lean`  
**Source SHA-256:** `fbb6b498f04c04acf21ab84c55f1ac32093bac845a08a6daae69d20f5820e221`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `SameNormalizedResponse` | `DEF` | 19-23 | division-free cross-product relation |
| `n001ConductanceUnit` | `DEF` | 24-27 | rational lift of N001 |
| `n001ConductanceUnit_eq_one` | `THEOREM` | 28-38 | exact lift theorem |
| `commonPositiveRescalingPreservesNormalizedResponse` | `THEOREM` | 39-55 | common positive scaling theorem |
| `n001CanonicalRepresentativeForPositiveUnit` | `THEOREM` | 56-73 | canonical-representative theorem |

**Registered anchors for M005:** 9. Every path, line range and source hash is also present in `derivation/registry/documentation/CODE_ANCHORS.tsv`.
