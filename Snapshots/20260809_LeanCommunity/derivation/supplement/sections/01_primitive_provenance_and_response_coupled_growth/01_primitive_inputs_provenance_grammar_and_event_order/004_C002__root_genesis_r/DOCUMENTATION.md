# 004 · C002 — Root genesis r

**Canonical node label:** `004 · C002`  
**Semantic ID:** `C002`  
**Current section path:** `1.1.4`  
**Documentation tier:** `D1`  
**Documentation state:** `COMPLETE_V2`

## Position In Derivation

`C002` is canonical node 004. Its only hard predecessor is `003 · C001`, the unique empty carrier. The node is the first construction that changes the cardinality of the provenance carrier: before it, no provenance node exists; after it, exactly the root exists.

The order is essential. Neither `I001` nor `I002` is needed to create the root, and no address grammar is available yet. Hence root genesis is independent of branching multiplicity and finite cutoff. The hard incoming edge is `E003: C001 -> C002` with relation `root_genesis`; the outgoing edge is `E004: C002 -> C003` with relation `anchors_provenance_grammar`.


<!-- CNNA-ARCHITECTURE-BEGIN C002 -->
## CNNA Architecture Role

C002 is the first realization in **ComplemeNt Net Architecture**: the empty carrier becomes a carrier with one born root. The root has no permanent intrinsic opposite; its continuation complement is introduced only when C003/C018 define and order the not-yet-realized slots. This is an interpretation of the existing genesis contract, not extra mathematical content.
<!-- CNNA-ARCHITECTURE-END C002 -->

## Mathematical Contract

Let

\[
X_\varnothing=(V_\varnothing,R_\varnothing),\qquad V_\varnothing=\varnothing,\quad R_\varnothing=\varnothing
\]

be the C001 state. `C002` defines one transition

\[
\Gamma_r(X_\varnothing)=X_r,
\]

such that

\[
V(X_r)=\{r\},\qquad R(X_r)=\varnothing.
\]

The complete local contract is:

1. the root token `r` exists;
2. the post-genesis carrier contains exactly `r`;
3. no ordered pair is a relation;
4. `r` has no provenance parent;
5. no geometric position is assigned;
6. no address, node ID, rank, event index, conductance, load or response is introduced.

The contract is about the **immediate post-genesis state**. It does not claim that the root remains relation-free after later births.

## Introduction Reason

The empty carrier alone does not supply a node on which later provenance addresses or relations can be based. `C002` isolates the irreducible birth of the root from every downstream structure. This separation prevents the root address, first edge or first conductance from being mistaken for primitive content of genesis.

## Explicit Construction

### Mathematical construction

Introduce a single zero-payload symbol `r`. Define the carrier `X_r` by the singleton node set and empty relation set above. Define parenthood and geometric-position predicates for `r` to be false at this stage.

### Python construction

Python uses two frozen, slotted, zero-field dataclasses:

- `Root` is the root token type;
- `RootedCarrier` is the post-genesis carrier type.

`ROOT` and `ROOTED_CARRIER` are their canonical values. `RootedCarrier.nodes` returns `(ROOT,)`, `relations` returns `()`, `contains_node` recognizes only `ROOT`, and `contains_relation` is constantly false. `root_genesis` accepts exactly an `EmptyCarrier` value and returns `ROOTED_CARRIER`.

### Lean construction

Lean uses singleton inductive types `Root` and `RootedCarrier`. Membership is represented by

```lean
node = Root.canonical
```

and relation, parent and position predicates are definitionally `False`. The transition

```lean
def rootGenesis (_carrier : EmptyCarrier) : RootedCarrier :=
  RootedCarrier.canonical
```

is total on the C001 type and contains no branch or selected witness.

## Invariants

The construction establishes the following invariants:

| Invariant | Formal content | Evidence |
|---|---|---|
| Singleton node content | every admitted node equals `Root.canonical` | Lean `rootPresent`, `nodeUnique`; Python `nodes == (ROOT,)` |
| Empty relation content | no source-target pair belongs | Lean `ContainsRelation := False`, `noRelation`; Python `relations == ()` |
| Parentlessness | no parent value can witness parenthood of the root | Lean `HasParent := False`, `rootHasNoParent`; Python `parent_of(ROOT) is None` |
| No geometry | no position value can witness a root position | Lean `HasGeometricPosition := False`, `rootHasNoGeometricPosition`; Python metadata-reflection test |
| Zero local payload | root and carrier have no data fields | Python dataclass reflection; Lean one-constructor inductives |

The distinction between “one carrier value” and “one provenance node” is explicit: `RootedCarrier` is the state representation; `Root.canonical` is the sole provenance node inside it.

## Canonicity Or Uniqueness

Lean proves two separate uniqueness statements:

\[
\forall r':\mathrm{Root},\quad r'=r,
\]

and

\[
\forall X':\mathrm{RootedCarrier},\quad X'=X_r.
\]

These are `Root.eqCanonical` and `RootedCarrier.eqCanonical`. Since `EmptyCarrier` is itself unique, `rootGenesis_eqCanonical` shows that every admissible source representation produces the same rooted carrier. Thus no hidden root choice, carrier choice or genesis seed occurs at C002.

Python provides the executable analogue: zero-field dataclass instances compare equal, canonical constants are returned, and there is no instance dictionary in which hidden state could be stored.

## Boundary Cases

- **No self-edge:** `(r,r)` is not a relation. Root birth is not first-relation birth.
- **No parent sentinel as data:** Python returns `None` from `parent_of(ROOT)`, but Lean states the stronger proposition that no parent witness exists. `None` is an API representation, not a mathematical parent value.
- **Exact source domain:** Python rejects `None`, tuples, arbitrary objects, the root token and the already rooted carrier as genesis inputs. Only C001's carrier type is accepted.
- **No downstream metadata:** addresses, depths, ranks, event indices, conductances, responses and coordinates are absent.
- **No dependence on `b` or `L`:** neither parameter occurs in the constructor or theorem signatures.

## Python Lean Cross Layer

| Contract component | Python | Lean | Agreement |
|---|---|---|---|
| Root token | zero-field `Root` dataclass | singleton `Root` inductive | unique zero-payload value |
| Rooted state | zero-field `RootedCarrier` dataclass | singleton `RootedCarrier` inductive | unique carrier representation |
| Node membership | equality with `ROOT` | `node = Root.canonical` | exact singleton membership |
| Relation membership | always `False` | proposition `False` | exact empty relation set |
| Genesis map | runtime type check, canonical return | total function on `EmptyCarrier` | same mathematical domain and value |
| Uniqueness evidence | equality/reflection tests | kernel theorems | executable check plus formal proof |

There is no known cross-layer mismatch. Python performs explicit dynamic rejection because its type annotations are not runtime proofs; Lean's function domain already excludes invalid source types.

## Countercheck

The node-local Python suite contains four targeted tests:

| Test | Lines | Failure excluded |
|---|---:|---|
| `test_genesis_creates_exactly_one_root_and_no_relation` | 22-28 | extra node or relation, including a self-edge |
| `test_root_is_unique_zero_payload_and_has_no_parent` | 30-38 | hidden dataclass payload or parent |
| `test_c002_does_not_smuggle_downstream_metadata` | 40-60 | address, geometry, event, conductance or response fields |
| `test_genesis_domain_is_exactly_empty_carrier` | 62-67 | coercion from unrelated source objects |

Lean separately proves the positive singleton statement and the three negative predicates. The combination is stronger than either an executable example or a type-level singleton alone.

## Result

`C002` closes the structural statement:

> From the unique empty carrier there is a canonical root-genesis transition to a unique carrier containing exactly one zero-payload root and no relation; the root has no parent or geometry at this derivation stage.

No later structure is included in this result. The node remains frozen under the existing core gate; the documentation update does not alter its Python or Lean source.

## Downstream Handoff

- `E003` is the completed incoming genesis edge from `C001`.
- `E004` passes the rooted carrier to `C003`.

At `C003`, the root token is anchored to the empty word. That anchoring is a new construction and must not be read backward into C002.

## Code Anchors

### Python source

**Path:** `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s01_primitive_inputs_grammar_and_event_order/s04_c002__root_genesis_r.py`  
**Source SHA-256:** `889514d52db406e4a2ea975ecf9439e19fe52000431fce888ee98ced0b3482ef`

| Symbol | Kind | Lines | Role |
|---|---|---:|---|
| `Root` | `CLASS` | 22-23 | `SOURCE` |
| `RootedCarrier` | `CLASS` | 30-50 | `SOURCE` |
| `root_genesis` | `FUNCTION` | 56-65 | `SOURCE` |

### Python tests

**Path:** `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s01_primitive_inputs_grammar_and_event_order/test_s04_c002__root_genesis_r.py`  
**Source SHA-256:** `cbc246c9536122c79f031c7e79ea3f94bd39360c0566f1b58a3adf99ca5cf488`

| Symbol | Kind | Lines | Role |
|---|---|---:|---|
| `TestRootGenesis` | `CLASS` | 21-67 | `TEST` |

### Lean core

**Path:** `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S01_PrimitiveInputsGrammarAndEventOrder/S04_C002_RootGenesisR.lean`  
**Source SHA-256:** `f8e3f0a55eea3b91203686cfeb1950abddd39f5d66fb7c8e0b218a26863146a5`

| Symbol | Kind | Lines | Role |
|---|---|---:|---|
| `Root` | `INDUCTIVE` | 22-27 | `SOURCE` |
| `canonical` | `DEF` | 28-31 | `SOURCE` |
| `eqCanonical` | `THEOREM` | 32-38 | `SOURCE` |
| `RootedCarrier` | `INDUCTIVE` | 39-44 | `SOURCE` |
| `canonical` | `DEF` | 45-48 | `SOURCE` |
| `ContainsNode` | `DEF` | 49-52 | `SOURCE` |
| `ContainsRelation` | `DEF` | 53-57 | `SOURCE` |
| `HasParent` | `DEF` | 58-62 | `SOURCE` |
| `HasGeometricPosition` | `DEF` | 63-67 | `SOURCE` |
| `rootPresent` | `THEOREM` | 68-72 | `SOURCE` |
| `nodeUnique` | `THEOREM` | 73-77 | `SOURCE` |
| `noRelation` | `THEOREM` | 78-82 | `SOURCE` |
| `rootHasNoParent` | `THEOREM` | 83-88 | `SOURCE` |
| `rootHasNoGeometricPosition` | `THEOREM` | 89-94 | `SOURCE` |
| `eqCanonical` | `THEOREM` | 95-101 | `SOURCE` |
| `rootGenesis` | `DEF` | 102-105 | `SOURCE` |
| `rootGenesis_canonical` | `THEOREM` | 106-110 | `SOURCE` |
| `rootGenesis_eqCanonical` | `THEOREM` | 111-115 | `SOURCE` |
