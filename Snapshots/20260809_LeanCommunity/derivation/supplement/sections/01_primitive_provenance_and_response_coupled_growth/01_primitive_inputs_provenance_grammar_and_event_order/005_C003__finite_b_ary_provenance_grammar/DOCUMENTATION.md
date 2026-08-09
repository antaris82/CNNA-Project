# 005 · C003 — Finite b-ary provenance grammar

**Canonical node label:** `005 · C003`  
**Semantic ID:** `C003`  
**Current section path:** `1.1.5`  
**Documentation tier:** `D1`  
**Documentation state:** `COMPLETE_V2`

## Position In Derivation

`C003` is canonical node 005 and the first three-input join in the chain. Its hard predecessors are:

- `001 · I001` through `E001`, supplying $b\ge 2$;
- `002 · I002` through `E002`, supplying $L\ge 0$;
- `004 · C002` through `E004`, supplying the already-born canonical root.

The grammar must follow root genesis because it anchors an existing root token. It must follow both inputs because the slot alphabet depends on `b` and finite admission depends on `L`.


<!-- CNNA-ARCHITECTURE-BEGIN C003 -->
## CNNA Architecture Role

C003 supplies the first structural complement of **ComplemeNt Net Architecture**. Realized address prefixes and admissible right-extensions live in one bounded $b$-ary grammar, while the not-yet-realized continuations form the stage-relative open complement. No second external system is introduced.
<!-- CNNA-ARCHITECTURE-END C003 -->

## Mathematical Contract

Let

\[
S_b=\{0,1,\ldots,b-1\},\qquad b\ge2.
\]

An intrinsic provenance address is a finite word

\[
a=(a_1,\ldots,a_d)\in S_b^*,
\]

with depth $|a|=d$. The canonical root address is the empty word $\varepsilon$. For $u\in S_b^*$ and $q\in S_b$, define right extension

\[
\operatorname{snoc}(u,q)=u\Vert(q).
\]

The finite approximant at cutoff `L` admits

\[
\mathcal A_{b,L}=\{a\in S_b^*:|a|\le L\}.
\]

Every nonempty address has a unique decomposition

\[
a=u\Vert(q),
\]

which defines its immediate parent `u` and final slot/rank `q`. The contract owns exactly:

1. the local slot alphabet;
2. intrinsic finite words;
3. root anchoring to $\varepsilon$;
4. child extension;
5. depth, parent and final-rank recovery;
6. finite admission by $|a|\le L$.

It owns no event order, node ID, geometry, metric, conductance, response or dynamics.

## Introduction Reason

The rooted carrier from C002 contains a root token but no language for descendants. C003 introduces the minimal grammar needed to refer canonically to potential descendants without importing a temporal order or physical state. Separating the intrinsic word constructor from the finite cutoff is essential: `L` restricts the current approximant but must not change the local `b`-ary branching rule.

## Explicit Construction

### Intrinsic grammar

The alphabet is `S_b`. The root word is empty. `snoc` appends one slot at the right. The inverse operation `unsnoc?` returns `none` on the root and otherwise returns the prefix word and final slot.

The immediate parent relation is defined by

```text
Parent(u,a) iff parent?(a) = some(u).
```

Depth is word length. Therefore the grammar is rooted and ordered: the final symbol records the local child slot.

### Finite admission

A bounded address is a pair consisting of an intrinsic address and a proof that its depth is at most `L`. The bounded child constructor additionally requires a proof that the successor depth remains within the cutoff.

This gives two distinct layers:

\[
S_b^* \quad\text{(intrinsic grammar)}
\]

and

\[
\mathcal A_{b,L}\subseteq S_b^* \quad\text{(finite admitted carrier)}.
\]

### Root anchor and predecessor join

`FiniteBAryProvenanceGrammar` stores exactly the three predecessor objects: the C002 rooted carrier, I001 branching parameter and I002 cutoff. `rootAddress` maps the unique root token to the bounded empty word. The `build_*` equations expose that the canonical constructor preserves each predecessor without transformation.

## Invariants

| Invariant | Mathematical statement | Formal evidence |
|---|---|---|
| Root depth | $|\varepsilon|=0$ | `depth_root` |
| Successor depth | `|snoc(u,q)| = |u| + 1` | `depth_snoc`, bounded `child_depth` |
| Exact decomposition | `unsnoc?(snoc(u,q)) = (u,q)` | `unsnoc?_snoc` |
| Root parentlessness | $\operatorname{parent?}(\varepsilon)=\mathrm{none}$ | `parent?_root` |
| Root has no final rank | $\operatorname{finalSlot?}(\varepsilon)=\mathrm{none}$ | `finalSlot?_root` |
| Child parent equation | `parent?(snoc(u,q)) = some(u)` | `parent?_snoc`, `parent_snoc` |
| Child rank equation | `finalSlot?(snoc(u,q)) = some(q)` | `finalSlot?_snoc` |
| Parent uniqueness | equal child words imply equal prefixes | `snoc_parent_unique` |
| Slot uniqueness | equal child words imply equal final slots | `snoc_slot_unique` |
| Cutoff preservation | bounded child depth remains $\le L$ | `BoundedProvenanceAddress.child` |
| Root admission | empty word admitted for every `L`, including zero | `BoundedProvenanceAddress.root` |

These invariants show that parenthood and sibling rank are derivable from syntax. They are not independent node labels that could disagree with the address.

## Canonicity Or Uniqueness

Three distinct canonicity claims are established:

1. **Root anchor:** the unique C002 root maps to the empty word.
2. **Non-root decomposition:** a child word determines its parent and final slot uniquely.
3. **Predecessor join:** the grammar constructor contains exactly the supplied rooted carrier, branching parameter and cutoff.

No enumeration order is claimed. Multiple words at the same depth are incomparable until C018 supplies its BFS/lexicographic schedule. Hence C003 proves canonical syntax, not canonical time.

## Boundary Cases

### Zero cutoff

For $L=0$, the admitted carrier contains only $\varepsilon$. The intrinsic alphabet and `child_address` remain defined, but no non-root child is admitted into the finite approximant.

### Root operations

The root has no parent and no final rank. Python raises `ValueError`; Lean returns `none`. These are equivalent partial-operation encodings.

### Invalid slots and addresses

Ranks below zero or at least `b` are rejected. Python additionally rejects Boolean, floating-point, string and `None` ranks, and rejects list-based addresses because the executable canonical representation is a tuple. Lean prevents out-of-range slots by the type `Fin b.value`.

### Cutoff independence

The intrinsic constructor can produce a word deeper than `L`; the bounded grammar then rejects it. This countercheck prevents the common but incorrect interpretation that the terminal level changes the slot alphabet or makes child extension undefined in the unbounded grammar.

## Python Lean Cross Layer

| Concept | Python | Lean | Semantic relation |
|---|---|---|---|
| Slot | built-in `int` checked against $0\le q<b$ | `Fin b.value` | same finite alphabet; Lean internalizes the bound |
| Address | `tuple[int, ...]` | `List (ProvenanceSlot b)` | same finite-word semantics |
| Root | empty tuple `()` | empty list `[]` | exact empty word |
| Child | tuple concatenation | recursive `snoc` | right extension |
| Parent/rank | slicing and final element | `unsnoc?`, projections | same unique decomposition |
| Cutoff | runtime length check | proof field `depth_le_cutoff` | same admitted words |
| Grammar join | frozen dataclass | structure | same three predecessors |

Python's `Address` type alias is not by itself a runtime proof; `validate_unbounded_address` supplies the checks. Lean's dependent slot type prevents malformed slot values from entering an address in the first place. Conversely, Python explicitly tests foreign runtime types that cannot inhabit the corresponding Lean types.

## Countercheck

The node-local Python suite contains eight targeted groups:

| Test | Lines | Property or failure excluded |
|---|---:|---|
| `test_three_predecessors_join_and_root_is_anchored_to_empty_word` | 31-38 | missing predecessor or nonempty root address |
| `test_slot_alphabet_is_exactly_zero_through_b_minus_one` | 40-46 | off-by-one slot alphabet |
| `test_child_parent_rank_and_depth_are_word_derived` | 48-61 | independent or inconsistent parent/rank/depth fields |
| `test_local_b_ary_word_constructor_is_independent_of_cutoff` | 63-70 | conflation of intrinsic grammar with finite admission |
| `test_zero_cutoff_is_root_only_for_admitted_words` | 72-83 | accidental non-root admission at `L=0` |
| `test_root_has_no_parent_or_final_rank` | 85-89 | fictitious root predecessor or rank |
| `test_invalid_ranks_addresses_and_predecessor_types_are_rejected` | 91-109 | malformed slots, addresses or predecessor types |
| `test_c003_adds_no_event_geometry_response_or_node_id_fields` | 111-122 | hidden schedule, geometry or physical state |

The nontrivial Lean proof chain is:

```text
unsnoc?_snoc
  -> parent?_snoc and finalSlot?_snoc
  -> parent_snoc
  -> snoc_parent_unique and snoc_slot_unique
```

with `depth_snoc` and bounded `child_depth` providing the independent depth/cutoff chain. These theorems establish the general identities that the Python cases instantiate.

## Result

`C003` closes the statement:

> Given the canonical root, branching parameter $b\ge 2$, and finite cutoff $L\ge 0$, there is a canonical finite b-ary provenance grammar whose nodes are bounded words, whose root is the empty word, and whose non-root addresses determine unique parents and final slots.

The result is grammatical and finite. It does not define a birth order, metric, conductance or response.

## Downstream Handoff

- `E005: C003 -> C004A` supplies the grammar for the first provenance slot.
- `E063: C003 -> C018` supplies the grammar to the separate canonical schedule construction.
- `E140` and `E149` expose future proof obligations for order and finite enumeration.
- `E402: C003 -> M050` remains blocked because provenance-derived metric selection is not established by the grammar alone.
- `E260` supports the later node-local metric-family proof gate.

The outgoing multiplicity reflects reuse of one grammar, not parallel versions of the DAG.

## Code Anchors

### Python source

**Path:** `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s01_primitive_inputs_grammar_and_event_order/s05_c003__finite_b_ary_provenance_grammar.py`  
**Source SHA-256:** `fa2ad5221cd2131508b98d54673a4cb8324e673d50b339a8aab857b69fe435cb`

| Symbol | Kind | Lines | Role |
|---|---|---:|---|
| `slot_alphabet` | `FUNCTION` | 35-39 | `SOURCE` |
| `validate_unbounded_address` | `FUNCTION` | 42-53 | `SOURCE` |
| `root_address` | `FUNCTION` | 56-58 | `SOURCE` |
| `child_address` | `FUNCTION` | 61-68 | `SOURCE` |
| `address_parent` | `FUNCTION` | 71-76 | `SOURCE` |
| `final_slot` | `FUNCTION` | 79-84 | `SOURCE` |
| `address_depth` | `FUNCTION` | 87-89 | `SOURCE` |
| `is_parent_of` | `FUNCTION` | 92-96 | `SOURCE` |
| `FiniteBAryProvenanceGrammar` | `CLASS` | 100-164 | `SOURCE` |
| `build_finite_b_ary_provenance_grammar` | `FUNCTION` | 167-173 | `SOURCE` |

### Python tests

**Path:** `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s01_primitive_inputs_grammar_and_event_order/test_s05_c003__finite_b_ary_provenance_grammar.py`  
**Source SHA-256:** `1d6630ef73e34981eacecbb02cd8100d8ae12f6aa5f28905ede76084fd02b581`

| Symbol | Kind | Lines | Role |
|---|---|---:|---|
| `TestFiniteBAryProvenanceGrammar` | `CLASS` | 25-122 | `TEST` |

### Lean core

**Path:** `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S01_PrimitiveInputsGrammarAndEventOrder/S05_C003_FiniteBAryProvenanceGrammar.lean`  
**Source SHA-256:** `81563345b44177915f32a03d6c42df7adfa1ca4176ab27d6569584105ad25866`

| Symbol | Kind | Lines | Role |
|---|---|---:|---|
| `ProvenanceSlot` | `ABBREV` | 26-28 | `SOURCE` |
| `ProvenanceAddress` | `ABBREV` | 29-33 | `SOURCE` |
| `root` | `DEF` | 34-37 | `SOURCE` |
| `snoc` | `DEF` | 38-42 | `SOURCE` |
| `depth` | `DEF` | 43-46 | `SOURCE` |
| `depth_root` | `THEOREM` | 47-50 | `SOURCE` |
| `depth_snoc` | `THEOREM` | 51-60 | `SOURCE` |
| `unsnoc` | `DEF` | 61-69 | `SOURCE` |
| `unsnoc` | `THEOREM` | 70-82 | `SOURCE` |
| `parent` | `DEF` | 83-88 | `SOURCE` |
| `finalSlot` | `DEF` | 89-94 | `SOURCE` |
| `Parent` | `DEF` | 95-98 | `SOURCE` |
| `parent` | `THEOREM` | 99-102 | `SOURCE` |
| `finalSlot` | `THEOREM` | 103-106 | `SOURCE` |
| `parent` | `THEOREM` | 107-112 | `SOURCE` |
| `finalSlot` | `THEOREM` | 113-118 | `SOURCE` |
| `parent_snoc` | `THEOREM` | 119-123 | `SOURCE` |
| `snoc_parent_unique` | `THEOREM` | 124-132 | `SOURCE` |
| `snoc_slot_unique` | `THEOREM` | 133-143 | `SOURCE` |
| `BoundedProvenanceAddress` | `STRUCTURE` | 144-151 | `SOURCE` |
| `root` | `DEF` | 152-157 | `SOURCE` |
| `child` | `DEF` | 158-168 | `SOURCE` |
| `root_address` | `THEOREM` | 169-173 | `SOURCE` |
| `child_address` | `THEOREM` | 174-181 | `SOURCE` |
| `child_depth` | `THEOREM` | 182-192 | `SOURCE` |
| `FiniteBAryProvenanceGrammar` | `STRUCTURE` | 193-200 | `SOURCE` |
| `build` | `DEF` | 201-207 | `SOURCE` |
| `rootPresent` | `THEOREM` | 208-212 | `SOURCE` |
| `rootAddress` | `DEF` | 213-217 | `SOURCE` |
| `rootAddress_canonical` | `THEOREM` | 218-222 | `SOURCE` |
| `rootAddress_unique` | `THEOREM` | 223-227 | `SOURCE` |
| `build_rootedCarrier` | `THEOREM` | 228-232 | `SOURCE` |
| `build_branching` | `THEOREM` | 233-237 | `SOURCE` |
| `build_cutoff` | `THEOREM` | 238-244 | `SOURCE` |

<!-- CNNA-OPEN-PROVENANCE-BEGIN C003 -->
## Open-provenance role: Provenance-complete carrier

C003 supplies the finite event-address grammar of the current CNNA specialization.  In the generalized open-provenance interpretation it is the carrier on which immutable event provenance can be recorded; it does not by itself assert that every empirical system has such a carrier.

<!-- CNNA-OPEN-PROVENANCE-END C003 -->
