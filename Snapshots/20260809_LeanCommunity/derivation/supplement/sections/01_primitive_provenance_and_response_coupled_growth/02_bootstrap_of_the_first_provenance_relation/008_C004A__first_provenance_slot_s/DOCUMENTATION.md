# 008 · C004A — First provenance slot s₁

**Canonical node label:** `008 · C004A`  
**Semantic ID:** `C004A`  
**Current section path:** `1.2.1`  
**Documentation tier:** `D1`  
**Documentation state:** `COMPLETE_V2`

## Position In Derivation

`C004A` is canonical node 008 and the first node of the bootstrap group. Its verified hard predecessors are:

- `E005: C003 -> C004A`, supplying the finite b-ary provenance grammar;
- `E064: C018 -> C004A`, supplying the canonical breadth-first/lexicographic order.

The node must follow both predecessors. C003 alone gives the root, the slot alphabet and address extension, but does not select a first non-root address. C018 alone gives an order parameterized by a grammar, but cannot identify a slot without the same C003 instance. C004A joins these inputs and selects the first structural slot. The downstream edge `E007: C004A -> C013` is `ACTIVE_VERIFIED` and transfers the slot to the actual first-birth construction.


<!-- CNNA-ARCHITECTURE-BEGIN C004A -->
## CNNA Architecture Role

C004A is the first explicit complement handoff: it selects the least open continuation of the realized root but does not yet create a node or relation. The possibility becomes realized only at C013.
<!-- CNNA-ARCHITECTURE-END C004A -->

## Mathematical Contract

Let `G` be a C003 grammar with branching parameter $b\ge2$, root address $\varepsilon$, local slot alphabet

\[
S_b=\{0,1,\ldots,b-1\},
\]

and finite cutoff $L\ge0$. Let $\Sigma$ be the C018 schedule associated with the same grammar. The first provenance slot is the triple

\[
s_1=\bigl(\varepsilon,0,\varepsilon\Vert(0)\bigr)
   =\bigl(\varepsilon,0,(0)\bigr).
\]

Its contract is:

1. the parent is the C003 root $\varepsilon$;
2. the stored local sibling rank is zero;
3. the intrinsic child address is $(0)$;
4. $(0)$ is the minimum non-root address under the C018 order;
5. the address is admitted into the finite approximant exactly when its depth one satisfies $1\le L$;
6. the node performs no birth and carries no physical payload.

The notation $s_1$ is one-based ordinal prose. The internal C003/C018 rank is zero-based. Therefore $s_1$ means ``first slot'', not ``slot with rank one''.

## Introduction Reason

The derivation requires an exceptional bootstrap before the recurrent state exists. The root is already present, but there is not yet a born-prefix state from which a recurrent least-open slot could be selected. C004A therefore isolates the one structural slot that can be selected without any prior non-root birth: the rank-zero child of the root under the already-fixed C018 convention.

Keeping this selection separate from C013 is scientifically necessary. The address $(0)$ is a provenance possibility. A birth additionally requires finite-cutoff admission and later construction of a new carrier state, directed relation and conductance data. Conflating those operations would hide the exceptional bootstrap assumption inside an address definition.

## Explicit Construction

### Predecessor object

The Python and Lean objects carry the same direct predecessor data:

```text
grammar  : C003 FiniteBAryProvenanceGrammar
schedule : C018 CanonicalBirthSchedule
coherence: schedule.grammar = grammar
```

Python checks the coherence dynamically in `__post_init__`. Lean stores it as the proof field `schedule_grammar`.

### Derived rank

The active domain $b\ge2$ guarantees that zero is a valid local slot. Lean internalizes this by constructing

```text
firstRank S : Fin S.grammar.branching.value
```

with value zero and a proof that $0<b$. Python obtains the same value from the first element of the exact tuple `grammar.slots = (0,...,b-1)`.

### Derived parent and address

The parent is not stored independently:

\[
\operatorname{parentAddress}(s_1)=\varepsilon.
\]

The address is C003 right extension:

\[
\operatorname{address}(s_1)
 =\operatorname{snoc}(\varepsilon,0)
 =(0).
\]

This construction is intrinsic and does not consult `L`.

### Cutoff gate

Finite admission is the proposition

\[
\operatorname{WithinCutoff}(s_1)
\iff
|\operatorname{address}(s_1)|\le L.
\]

Because the depth is exactly one, positive cutoffs admit the slot and zero cutoff rejects it. Python exposes the Boolean `admitted_by_cutoff` and the partial operation `require_admitted_address`; Lean exposes the proposition `WithinCutoff` and separate proofs for the positive and zero cases.

## Invariants

| Invariant | Mathematical statement | Formal evidence |
|---|---|---|
| Predecessor coherence | schedule and slot use one C003 grammar | Python `__post_init__`; Lean `schedule_grammar` |
| Least local rank | $\operatorname{rank}(s_1)=0$ | Python `rank`; Lean `firstRank_val` |
| Root parent | $\operatorname{parent}(s_1)=\varepsilon$ | Python `parent`; Lean `parentAddress_root` |
| Intrinsic address | $\operatorname{addr}(s_1)=\varepsilon\Vert0=(0)$ | Python `address`; Lean `address_eq_snoc` |
| Depth | $|\operatorname{addr}(s_1)|=1$ | Lean `address_depth`; Python tuple length |
| Parent recovery | `parent?((0)) = some(ε)` | Lean `address_parent`; Python C003 parent operation |
| Rank recovery | `finalSlot?((0)) = some(0)` | Lean `address_finalSlot`; Python C003 final-rank operation |
| Root-sibling minimality | $(0)$ precedes every root child of nonzero rank | `firstRank_eq_or_before`, `address_before_distinct_root_sibling` |
| Global non-root minimality | every non-root address equals $(0)$ or follows it | `address_eq_or_before_nonroot` |
| Strict global minimum | every distinct non-root address follows $(0)$ | `address_before_distinct_nonroot` |
| Positive-cutoff admission | $1\le L\Rightarrow(0)\in\mathcal A_{b,L}$ | `withinCutoff_of_one_le` |
| Zero-cutoff exclusion | $L=0\Rightarrow(0)\notin\mathcal A_{b,0}$ | `notWithinCutoff_at_zero` |

Parent, rank, address and admission are derived facts. They cannot be supplied as mutually inconsistent constructor fields.

## Canonicity Or Uniqueness

The sources establish canonicity at three levels.

### Local-rank canonicity

For every local slot $r\in S_b$,

\[
r=0\quad\lor\quad 0<r.
\]

Lean theorem `firstRank_eq_or_before` expresses exactly this dichotomy as equality with `firstRank` or strict C018 slot precedence.

### Address canonicity

For every non-root address $c$,

\[
c=(0)\quad\lor\quad(0)\prec_{\mathrm{BFSlex}}c.
\]

The proof splits the address syntax:

- the empty word contradicts non-rootness;
- a depth-one word is either rank zero or a later sibling;
- a word of depth at least two follows $(0)$ by breadth-first depth priority.

Together with C018 irreflexivity, this makes $(0)$ the unique minimum non-root address.

### Constructor canonicity boundary

`build_canonical_first_provenance_slot` and Lean `build` use the active C018 constructor. The formal source does not separately state a theorem that all inhabitants of the `FirstProvenanceSlot` structure are definitionally equal. The proved scientific claim is the canonicity of the extracted parent/rank/address data under coherent C003/C018 predecessors, not an overstrong global structure-equality theorem.

## Boundary Cases

### Cutoff L = 0

The C003 intrinsic word $(0)$ exists, and C004A still computes the same structural slot. However:

\[
\mathcal A_{b,0}=\{\varepsilon\},
\qquad
(0)\notin\mathcal A_{b,0}.
\]

Python therefore has `schedule.slots == ()`, `admitted_by_cutoff == False`, and `require_admitted_address()` raises `ValueError`. Lean theorem `notWithinCutoff_at_zero` proves the same exclusion proposition. No first non-root birth is possible at `L=0`.

### Positive cutoff

For every tested and proved $L\ge1$, $(0)$ is admitted. This gate only returns or proves an admissible address; it does not perform C013.

### One-based name versus zero-based rank

Replacing rank zero by rank one would select the second child and violate both C018 minimality and the source tests. The notation and stored rank must therefore remain distinct.

### Incoherent predecessors

A grammar paired with a schedule based on another grammar is rejected. Without this condition, the rank/address projection could be interpreted in a different branching or cutoff context from the schedule order.

### Active branching domain

The proof uses the project domain $b\ge2$. The existence of rank zero would require only a nonempty alphabet, but C004A does not enlarge or alter the active CNNA input domain fixed by I001.

## Python Lean Cross Layer

| Concept | Python | Lean | Semantic relation |
|---|---|---|---|
| C004A carrier | frozen dataclass `FirstProvenanceSlot` | structure `FirstProvenanceSlot` | same two direct predecessors |
| predecessor coherence | runtime equality check | proof field `schedule_grammar` | same grammar identity condition |
| first rank | `grammar.slots[0]` | `Fin` value `0` with bound proof | same zero-based local slot |
| parent | `grammar.root` | `ProvenanceAddress.root` | same empty word |
| address | `child_address(..., (), 0)` | `ProvenanceAddress.snoc root firstRank` | same word $(0)$ |
| cutoff admission | Boolean and rejecting accessor | proposition and theorems | same depth-one inequality |
| C018 minimality | first schedule element and `slot_precedes` tests | general theorems over all non-root addresses | Lean proves the universal statement exercised finitely by Python |
| payload boundary | dataclass field audit | structure fields only | no birth/physical payload in either layer |

Python's `schedule.slots[0]` is available only for positive cutoff, whereas C004A's structural `address` is available independently of cutoff. Lean encodes the structural side directly and treats finite admission as a proposition. This is a representation difference, not a semantic mismatch.

## Countercheck

The node-local Python suite contains eight targeted tests.

| Test | Lines | Property or failure excluded |
|---|---:|---|
| `test_s1_is_root_rank_zero_and_address_zero` | 25-32 | wrong parent, off-by-one rank or wrong child word across $b,L$ samples |
| `test_one_based_name_does_not_shift_zero_based_rank` | 34-37 | confusion of ordinal $s_1$ with rank one |
| `test_c018_selects_s1_as_first_admitted_slot_when_L_positive` | 39-52 | disagreement with C018 enumeration or reverse precedence |
| `test_L_zero_retains_structural_slot_but_admits_no_birth_slot` | 54-60 | conflation of structural word with finite admission |
| `test_positive_cutoff_admits_s1_without_performing_birth` | 62-67 | failure of the depth-one cutoff gate or hidden birth side effect |
| `test_two_direct_predecessors_must_share_same_grammar` | 69-74 | incoherent C003/C018 predecessor join |
| `test_invalid_predecessor_types_are_rejected` | 76-84 | acceptance of foreign runtime values |
| `test_payload_contains_only_direct_predecessors` | 86-100 | hidden geometry, IDs, event time, conductance or response |

The nontrivial Lean chain is:

```text
firstRank_eq_or_before
  -> address_before_distinct_root_sibling

address_depth
  + firstRank_eq_or_before
  + C018.shallower_before
  -> address_eq_or_before_nonroot
  -> address_before_distinct_nonroot

address_depth
  -> withinCutoff_of_one_le
  -> notWithinCutoff_at_zero
```

The first chain proves local minimality, the second upgrades it to all non-root addresses, and the third isolates finite-cutoff admissibility. These are logically distinct obligations.

## Result

`C004A` closes the statement:

> Given a C003 grammar and its coherent C018 schedule, the canonical first structural provenance slot has root parent, zero-based rank zero and address $(0)$. This address is the unique minimum non-root address under the C018 order and belongs to the finite approximant exactly when $L\ge1$.

The result is structural. It does not create the first non-root carrier element or any directed relation.

## Downstream Handoff

- `E005: C003 -> C004A` supplies the address grammar and root.
- `E064: C018 -> C004A` supplies the strict schedule order.
- `E007: C004A -> C013` is `ACTIVE_VERIFIED` and supplies the first slot to the first non-root birth construction.

C013 additionally consumes A001 and N001 and requires cutoff admission. It owns the newborn vertex, the first directed relation and the initial conductances. C004A owns none of those objects.

## Code Anchors

### Python source

**Path:** `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/s01_c004a__first_provenance_slot_s1.py`  
**Source SHA-256:** `b25b3e8a8c9f22c2611efe064c002af3690874c16a1a8ab51e68f6238dc70de8`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `FirstProvenanceSlot` | `CLASS` | 36-82 | coherent predecessor carrier, derived slot data and cutoff gate |
| `build_first_provenance_slot` | `FUNCTION` | 85-90 | explicit two-predecessor constructor |
| `build_canonical_first_provenance_slot` | `FUNCTION` | 93-99 | constructor using the active C018 schedule |

### Python tests

**Path:** `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s02_bootstrap_of_the_first_relation/test_s01_c004a__first_provenance_slot_s1.py`  
**Source SHA-256:** `2958ae8e902dea945ed5032ffff08806f43005c64b04f642e341c44a37db2c11`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `TestFirstProvenanceSlot` | `CLASS` | 19-100 | eight executable contract and negative-control tests |

### Lean core

**Path:** `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S02_BootstrapOfTheFirstRelation/S01_C004A_FirstProvenanceSlotS1.lean`  
**Source SHA-256:** `5e3fffc01b8d380d477130872955ba9348ae8c0af813e18d07801438ca8b9947`

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `FirstProvenanceSlot` | `STRUCTURE` | 23-30 | C003/C018 predecessor carrier with coherence proof |
| `fromPredecessors` | `DEF` | 31-39 | explicit coherent predecessor constructor |
| `build` | `DEF` | 40-45 | canonical constructor using C018 `build` |
| `firstRank` | `DEF` | 46-49 | bounded zero-based first slot |
| `parentAddress` | `DEF` | 50-53 | root parent definition |
| `address` | `DEF` | 54-57 | intrinsic child address $(0)$ |
| `firstRank_val` | `THEOREM` | 58-61 | rank value equation |
| `parentAddress_root` | `THEOREM` | 62-66 | parent equals root |
| `address_eq_snoc` | `THEOREM` | 67-71 | child-word construction equation |
| `address_depth` | `THEOREM` | 72-76 | exact depth one |
| `address_parent` | `THEOREM` | 77-88 | C003 parent recovery |
| `address_finalSlot` | `THEOREM` | 89-100 | C003 final-rank recovery |
| `firstRank_eq_or_before` | `THEOREM` | 101-112 | least local-rank dichotomy |
| `address_before_distinct_root_sibling` | `THEOREM` | 113-127 | strict precedence over other root children |
| `address_eq_or_before_nonroot` | `THEOREM` | 128-156 | global non-root minimum alternative |
| `address_before_distinct_nonroot` | `THEOREM` | 157-168 | strict global minimum for distinct addresses |
| `WithinCutoff` | `DEF` | 169-172 | finite-admission proposition |
| `withinCutoff_of_one_le` | `THEOREM` | 173-179 | positive-cutoff admission |
| `notWithinCutoff_at_zero` | `THEOREM` | 180-189 | zero-cutoff exclusion |

The canonical machine-readable register is `derivation/registry/documentation/CODE_ANCHORS.tsv`. The stable anchor identity is source path plus symbol plus source SHA-256; line numbers are a direct reading aid and are regenerated after source edits.
