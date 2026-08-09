# CNNA cross-language semantic identity policy

Status: **binding for every not-yet-frozen SOLL node**.

## Core invariant

Python and Lean may be asymmetric or complementary in representation, algorithm, data structures, and proof organization.  They must nevertheless identify **the same mathematical object** for every SOLL node.  Paper and Supplement must identify that same object as well.

For a SOLL node `K`, the required condition is semantic identity, not source-code isomorphism:

```text
Sem_Python(K)  ≅  Sem_Lean(K)  ≅  Sem_Paper(K).
```

Here `≅` must be made explicit at the mathematically correct level: equality, extensional equality, canonical isomorphism, equality of a subspace/subalgebra, or restriction/completion compatibility.  The equivalence notion itself is part of the node contract and may not be chosen after seeing the result.

## Mandatory locks before freeze

Every open node must lock all of the following where applicable:

1. **Domain identity.** Same admissible inputs and same excluded inputs.
2. **Object identity.** Same function, relation, set, slot, cut, matrix/operator, state, algebra, map, theorem proposition, or obstruction claim.
3. **Boundary-case identity.** Saturation, empty cases, singular blocks, index endpoints, zero modes, and failure behavior agree.
4. **Ordering/basis identity.** Any indexed object uses the same canonical carrier and an explicit permutation/transport if representations differ.
5. **Canonicity/uniqueness identity.** A node advertised as canonical or unique may not hide a language-specific convention.
6. **Exactness identity.** Numerical tolerance is evidence machinery only unless tolerance is explicitly part of the mathematical object.
7. **Partiality identity.** Python exceptions/`None`/rejection conditions correspond exactly to Lean hypotheses, predicates, `Option`, or domain theorems.
8. **Limit/completion identity.** Finite Python representatives count only when proved to be canonical restrictions, cylinders, or compressions of the same completed/infinite object formalized analytically.
9. **Theorem identity.** Python tests can witness instances; they never silently weaken or strengthen the universal Lean theorem.
10. **Obstruction identity.** A numerical failure or failed candidate rules out only the precisely stated candidate/domain unless a theorem proves more.
11. **Control isolation.** Supplementary controls identify the same modified mathematical rule in both languages and never alter the main DAG.

## Language asymmetry

Allowed examples:

- Python: finite enumeration; Lean: strict-order characterization.
- Python: executable constructor; Lean: uniqueness predicate/theorem.
- Python: exact finite matrices; Lean: operator/map formulation.
- Python: canonical finite compressions; Lean: completed/infinite operator.
- Python: falsification/property tests; Lean: universal theorem.

These are valid only with an explicit bridge showing that both sides identify the same object.

## Forbidden

- A Python-only or Lean-only **scientific** object inserted to make one implementation easier.
- A new SOLL node whose only purpose is language-specific implementation machinery.
- Silent changes of domain, basis, indexing, sign, normalization, quotient, topology, completion, or failure convention.
- Treating floating-point agreement or tolerance closure as the definition of an exact algebraic object.
- Treating finite numerical evidence as proof of an infinite/completed statement.

Language-specific helper definitions, lemmas, tests, local structures, and implementation functions are allowed inside the owning SOLL node.  They are not DAG nodes and must not acquire independent scientific semantics.

## C004 reference pattern

For C004 the permitted asymmetry is exemplary:

```text
Python:  schedule.slots[n]
Lean:    the uniquely least C018-open slot after the C005 initial segment
```

The required bridge is that these characterize the same `s_{n+1}`, including the finite saturation case `n = N` where no next slot exists.

## Audit binding

`derivation/registry/derived/CROSS_LANGUAGE_SEMANTIC_AUDIT.tsv` is a persistent prospective ledger.  It records the required bridge for every node that was open when this policy was introduced and must be extended for every future SOLL node before implementation.  Rows are not removed after freezing.

For every node in this ledger, `validate_node_freeze.py` requires the node document to bind a verified bridge in `cross_layer` using:

- `semantic_identity_verified: true`;
- a nonempty `identity_kind` (for example `EXTENSIONAL_EQUALITY`, `CANONICAL_ISOMORPHISM`, `RESTRICTION_COMPATIBILITY`, or `SAME_PROPOSITION`);
- nonempty `identity_evidence`;
- `semantic_mismatch_known: false`.

Thus the policy is not documentation-only: a scoped open/future node cannot freeze without explicit same-object evidence.
